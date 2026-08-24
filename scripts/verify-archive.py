#!/usr/bin/env python3
"""Verify or regenerate the content-addressed research archive manifest."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path, PurePosixPath
import re
import sys


REPO = Path(__file__).resolve().parent.parent


def extended_path(path: Path) -> Path:
    """Use Win32's extended form so deep preserved paths remain readable."""

    resolved = path.resolve()
    raw = str(resolved)
    if sys.platform == "win32" and not raw.startswith("\\\\?\\"):
        return Path("\\\\?\\" + raw)
    return resolved


SCAN_REPO = extended_path(REPO)
MANIFEST = REPO / "archive" / "MANIFEST.sha256"
MANIFEST_RELATIVE = "archive/MANIFEST.sha256"
ROOTS = (SCAN_REPO / "archive", SCAN_REPO / "translation" / "archive")
LINE_RE = re.compile(r"^([0-9A-F]{64})  (.+)$")
# Local recovery copies of historical Lean build products and Python import
# caches may exist after a development replay, but `.gitignore` excludes them
# from the submitted repository. The `.olean` path/size/hash contracts live in
# the textual ledger; `.pyc` files are disposable interpreter caches.
LOCAL_RECOVERY_SUFFIXES = {".olean", ".pyc"}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def archive_files() -> dict[str, Path]:
    result: dict[str, Path] = {}
    for root in ROOTS:
        if not root.is_dir():
            raise RuntimeError(f"missing archive root: {root}")
        for path in root.rglob("*"):
            relative = path.relative_to(SCAN_REPO).as_posix()
            if relative == MANIFEST_RELATIVE:
                continue
            if path.suffix.lower() in LOCAL_RECOVERY_SUFFIXES:
                continue
            if path.is_symlink():
                raise RuntimeError(f"archive symlink is forbidden: {path}")
            if path.is_file():
                if relative in result:
                    raise RuntimeError(f"duplicate archive path: {relative}")
                result[relative] = path
    return result


def write_manifest() -> None:
    files = archive_files()
    lines = [f"{sha256(files[name])}  {name}" for name in sorted(files)]
    MANIFEST.write_bytes(("\n".join(lines) + "\n").encode("utf-8"))
    print(f"wrote {MANIFEST.relative_to(REPO)} with {len(lines)} entries")


def read_manifest() -> dict[str, str]:
    if not MANIFEST.is_file():
        raise RuntimeError(f"missing manifest: {MANIFEST}")
    result: dict[str, str] = {}
    for number, line in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), 1):
        match = LINE_RE.fullmatch(line)
        if match is None:
            raise RuntimeError(f"invalid manifest line {number}")
        digest, name = match.groups()
        pure = PurePosixPath(name)
        if pure.is_absolute() or ".." in pure.parts:
            raise RuntimeError(f"unsafe manifest path on line {number}: {name}")
        if name in result:
            raise RuntimeError(f"duplicate manifest path: {name}")
        result[name] = digest
    return result


def verify_manifest() -> None:
    expected = read_manifest()
    actual = archive_files()
    missing = sorted(set(expected) - set(actual))
    extra = sorted(set(actual) - set(expected))
    mismatches = [
        name for name in sorted(set(expected) & set(actual))
        if sha256(actual[name]) != expected[name]
    ]
    if missing or extra or mismatches:
        details = []
        details.extend(f"missing: {name}" for name in missing)
        details.extend(f"unmanifested: {name}" for name in extra)
        details.extend(f"hash mismatch: {name}" for name in mismatches)
        raise RuntimeError("archive verification failed\n" + "\n".join(details))
    total = sum(path.stat().st_size for path in actual.values())
    print(f"PASS: {len(actual)} archive files, {total} bytes, all SHA-256 values match")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write", action="store_true", help="regenerate the manifest"
    )
    args = parser.parse_args()
    if args.write:
        write_manifest()
    else:
        verify_manifest()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RuntimeError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
