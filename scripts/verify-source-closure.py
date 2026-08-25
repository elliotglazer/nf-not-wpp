#!/usr/bin/env python3
"""Verify the packaged translated-replay source closure against its TSV."""

from __future__ import annotations

import csv
import hashlib
from pathlib import Path, PurePosixPath
import sys


REPO = Path(__file__).resolve().parent.parent
PROOF = REPO / "Proof"
MANIFEST = REPO / "provenance" / "c18-source-closure.tsv"
EXPECTED_HEADER = [
    "module",
    "path",
    "sha256",
    "sourceResolution",
    "directImportCount",
]
EXPECTED_ROWS = 1537


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def main() -> int:
    failures: list[str] = []
    seen_modules: set[str] = set()
    seen_paths: set[str] = set()
    total_bytes = 0
    with MANIFEST.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if reader.fieldnames != EXPECTED_HEADER:
            raise RuntimeError(f"unexpected TSV header: {reader.fieldnames!r}")
        rows = list(reader)
    if len(rows) != EXPECTED_ROWS:
        failures.append(f"expected {EXPECTED_ROWS} rows, found {len(rows)}")
    for number, row in enumerate(rows, 2):
        module = row["module"]
        relative = PurePosixPath(row["path"])
        relative_text = relative.as_posix()
        if module in seen_modules:
            failures.append(f"line {number}: duplicate module {module}")
        seen_modules.add(module)
        if relative_text in seen_paths:
            failures.append(f"line {number}: duplicate path {relative_text}")
        seen_paths.add(relative_text)
        if relative.is_absolute() or ".." in relative.parts:
            failures.append(f"line {number}: unsafe path {relative_text}")
            continue
        path = PROOF.joinpath(*relative.parts)
        if not path.is_file():
            failures.append(f"line {number}: missing Proof/{relative_text}")
            continue
        total_bytes += path.stat().st_size
        actual = sha256(path)
        expected = row["sha256"]
        if actual != expected:
            failures.append(
                f"line {number}: hash mismatch for Proof/{relative_text}: {actual}"
            )
    if failures:
        raise RuntimeError("source-closure verification failed\n" + "\n".join(failures))
    print(
        f"PASS: {len(rows)} packaged replay modules, {total_bytes} bytes, "
        "all SHA-256 values match"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RuntimeError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
