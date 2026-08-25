#!/usr/bin/env python3
"""Reproduce the memory-bounded packaging of the generated WPP FV lemmas."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
REPO = HERE.parent
PROOF = REPO / "Proof"
REFERENCE = HERE / "reference" / "WPPCompactSyntaxFVExplicit.monolith.lean"
MANIFEST = (
    HERE
    / "archive"
    / "work"
    / "nf_wpp_clean_fol_2026-08-21"
    / "definition_leaves"
    / "generated"
    / "wpp_compact_syntax_fv_explicit_manifest.json"
)

MONOLITH_SHA256 = "E09FA6176086DFFA998C20DEF8A782252B9D50A0873181A32E1E2C887A6E65F4"
MANIFEST_SHA256 = "C9F50E461223DCA894313EB229071E7C60AF1720C803DF4A6E4C0F12B46F8DDF"
MODULE = "WPPCompactSyntaxFVExplicit"
NAMESPACE = "NFChoice.Compiler.WPPCompactSyntaxFVExplicit"
THEOREM_COUNT = 143

# Fixed cumulative theorem ordinals.  The first nine declarations contain the
# three expensive generated proofs, so they are split more finely; the
# remaining byte-balanced shards stay near 10--11 KiB.
CUTS = (3, 6, 9, 29, 48, 67, 89, 104, 124, 143)

# Filled from one checked run of this script.  These hashes cover the exact
# LF-encoded packaging, independently of the byte comparison with Proof/.
EXPECTED_OUTPUTS = {
    "WPPCompactSyntaxFVExplicit.lean":
        "2E0C321BA7C80D941ABA929B1CD261F86C3E5525B4C23BEF3277686C25583005",
    "WPPCompactSyntaxFVExplicitPart001.lean":
        "35D7322965C12D902CBF9EF0D59C62A96646326F77A6E039223C9B502A261D2D",
    "WPPCompactSyntaxFVExplicitPart002.lean":
        "EBC2A49D1C790C8B07DBB5A0938AB5DB669CDC4B5268FA90889778ACFD8DFBB4",
    "WPPCompactSyntaxFVExplicitPart003.lean":
        "05BFA2F416891AAA3D084AABAA9796E168FED217E1F737484EB07996E7FD8F54",
    "WPPCompactSyntaxFVExplicitPart004.lean":
        "ED73579627B26414AD2A4429AF191B13CE4605C09AFF8BCBD45264546F8AEC7D",
    "WPPCompactSyntaxFVExplicitPart005.lean":
        "BB6E8A14D6B92EE7C5850DB52E1E4A80D3934F90CA673C0B84DFD30C0A0CE964",
    "WPPCompactSyntaxFVExplicitPart006.lean":
        "BC1C0AA2F2F082C3087A21DC72E826C40B716A0F8AEEE48D68F4290DCE9EDDBD",
    "WPPCompactSyntaxFVExplicitPart007.lean":
        "F7ABDECEE31C123C318366B9740F8E692BDF5DA5A7DAD9A2AE4830DD3E15047F",
    "WPPCompactSyntaxFVExplicitPart008.lean":
        "8F3D5DDE519C0F5E3FE787CA0DCDC63FAE354CBF3F26F068B8D6A00A8E296218",
    "WPPCompactSyntaxFVExplicitPart009.lean":
        "F82A7FD75FFB4C9ADE3F5BD829B63284C25947FD0995A19C011BDF86F854D94B",
    "WPPCompactSyntaxFVExplicitPart010.lean":
        "29E20DA7DD737F0514D4ECB1F639F30742CFE6662E6298C8DD71EC804E994C7F",
}

THEOREM_RE = re.compile(rb"(?m)^theorem ([A-Za-z0-9_']+)")
REFERENCE_RE = re.compile(
    rb"NFChoice\.Compiler\.WPPCompactSyntaxFVExplicit\."
    rb"(fv_syn_[A-Za-z0-9_']+)"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def checked_bytes(path: Path, expected: str, description: str) -> bytes:
    if not path.is_file():
        raise RuntimeError(f"missing {description}: {path}")
    data = path.read_bytes()
    actual = sha256_bytes(data)
    if actual != expected:
        raise RuntimeError(
            f"{description} hash mismatch: expected {expected}, found {actual}"
        )
    return data


def manifest_names() -> list[str]:
    raw = checked_bytes(MANIFEST, MANIFEST_SHA256, "frozen FV manifest")
    manifest = json.loads(raw)
    if manifest.get("definition_count") != THEOREM_COUNT:
        raise RuntimeError("frozen FV manifest does not contain 143 definitions")
    if manifest.get("namespace") != NAMESPACE:
        raise RuntimeError("frozen FV manifest namespace changed")
    mapping = manifest.get("label_to_lemma")
    if not isinstance(mapping, dict) or len(mapping) != THEOREM_COUNT:
        raise RuntimeError("frozen FV manifest lemma map changed")
    prefix = NAMESPACE + "."
    names: list[str] = []
    for qualified in mapping.values():
        if not isinstance(qualified, str) or not qualified.startswith(prefix):
            raise RuntimeError(f"invalid frozen FV lemma name: {qualified!r}")
        names.append(qualified.removeprefix(prefix))
    return names


def split_monolith(source: bytes) -> tuple[list[str], list[bytes], bytes]:
    matches = list(THEOREM_RE.finditer(source))
    if len(matches) != THEOREM_COUNT:
        raise RuntimeError(
            f"monolith contains {len(matches)} theorem declarations, expected 143"
        )
    names = [match.group(1).decode("ascii") for match in matches]
    expected_names = manifest_names()
    if names != expected_names:
        raise RuntimeError("monolith theorem order differs from the frozen FV manifest")

    namespace_line = f"namespace {NAMESPACE}".encode()
    namespace_start = source.find(namespace_line)
    end_line = f"end {NAMESPACE}".encode()
    end_start = source.rfind(end_line)
    if namespace_start < 0 or end_start < matches[-1].start():
        raise RuntimeError("monolith namespace envelope is malformed")
    if b"\r" in source:
        raise RuntimeError("monolith must retain its canonical LF encoding")

    prelude = source[namespace_start:matches[0].start()]
    blocks: list[bytes] = []
    for ordinal, match in enumerate(matches):
        stop = matches[ordinal + 1].start() if ordinal + 1 < len(matches) else end_start
        blocks.append(source[match.start():stop])

    ordinal_by_name = {name: ordinal for ordinal, name in enumerate(names)}
    for ordinal, block in enumerate(blocks):
        for reference in REFERENCE_RE.findall(block):
            name = reference.decode("ascii")
            referenced = ordinal_by_name.get(name)
            if referenced is None:
                raise RuntimeError(f"unknown internal FV reference: {name}")
            if referenced >= ordinal:
                raise RuntimeError(
                    f"FV dependency is not backward: {names[ordinal]} -> {name}"
                )
    return names, blocks, prelude


def generated_outputs(source: bytes) -> dict[str, bytes]:
    _names, blocks, prelude = split_monolith(source)
    outputs: dict[str, bytes] = {}
    start = 0
    for part, stop in enumerate(CUTS, 1):
        if part == 1:
            imports = b"import WPPCompactSourceSyntax\nimport CompactSyntaxFVDisable\n\n"
        else:
            imports = f"import {MODULE}Part{part - 1:03d}\n\n".encode()
        body = b"".join(blocks[start:stop])
        outputs[f"{MODULE}Part{part:03d}.lean"] = (
            imports + prelude + body + f"end {NAMESPACE}\n".encode()
        )
        start = stop
    if start != THEOREM_COUNT:
        raise RuntimeError("fixed FV split does not cover all theorem declarations")
    outputs[f"{MODULE}.lean"] = f"import {MODULE}Part{len(CUTS):03d}\n".encode()
    return outputs


def bootstrap_reference() -> None:
    if REFERENCE.exists():
        raise RuntimeError(f"refusing to overwrite frozen reference: {REFERENCE}")
    current = PROOF / f"{MODULE}.lean"
    source = checked_bytes(current, MONOLITH_SHA256, "current FV monolith")
    REFERENCE.parent.mkdir(parents=True, exist_ok=True)
    REFERENCE.write_bytes(source)
    print(f"preserved monolith: {REFERENCE}")


def verify_generated_hashes(outputs: dict[str, bytes]) -> None:
    if set(EXPECTED_OUTPUTS) != set(outputs):
        raise RuntimeError("script has no complete frozen output-hash inventory")
    failures: list[str] = []
    for name, generated in outputs.items():
        expected_hash = EXPECTED_OUTPUTS[name]
        actual_hash = sha256_bytes(generated)
        if actual_hash != expected_hash:
            failures.append(
                f"generated hash mismatch for {name}: expected {expected_hash}, found {actual_hash}"
            )
    if failures:
        raise RuntimeError("\n".join(failures))


def write_outputs(outputs: dict[str, bytes]) -> None:
    # Fail before touching Proof/ if the generator, cuts, or formatting no
    # longer reproduce the frozen package inventory.
    verify_generated_hashes(outputs)
    for name, data in outputs.items():
        (PROOF / name).write_bytes(data)
    for name in sorted(outputs):
        print(f"{sha256_bytes(outputs[name])}  Proof/{name}")
    # Re-read every file after writing rather than trusting write_bytes.
    verify_outputs(outputs)


def verify_outputs(outputs: dict[str, bytes]) -> None:
    verify_generated_hashes(outputs)
    failures: list[str] = []
    for name, generated in outputs.items():
        packaged = PROOF / name
        if not packaged.is_file() or packaged.read_bytes() != generated:
            failures.append(f"Proof/ byte comparison failed for {name}")
    if failures:
        raise RuntimeError("\n".join(failures))
    print(
        "PASS: frozen WPP FV monolith deterministically reproduces "
        f"all {len(outputs) - 1} shards and the import facade"
    )


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Reproduce and byte-check the generated WPP FV source shards"
    )
    parser.add_argument(
        "--bootstrap-reference",
        action="store_true",
        help="preserve the current hash-matched monolith before the initial split",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the deterministic shards and import facade under Proof/",
    )
    return parser


def main() -> int:
    args = make_parser().parse_args()
    if args.bootstrap_reference:
        bootstrap_reference()
    source = checked_bytes(REFERENCE, MONOLITH_SHA256, "frozen FV monolith")
    outputs = generated_outputs(source)
    if args.write:
        write_outputs(outputs)
    else:
        verify_outputs(outputs)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RuntimeError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
