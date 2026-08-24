#!/usr/bin/env python3
"""Regenerate and byte-check the accepted C18 Lean source chunk."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import sys

import portable_nominal_mm_translator_v2 as portable


HERE = Path(__file__).resolve().parent
REPO = HERE.parent
ARCHIVE = portable.ARCHIVE_WORKSPACE
HISTORICAL = (
    ARCHIVE / "work" / "nf_choice_clean_fol_2026-08-21" / "direct_nominal_prf_001"
)
SOURCE = (
    ARCHIVE
    / "work"
    / "mm0_conversion_2026-08-20"
    / "source_repair"
    / "hnwcut_resisomr_assist"
    / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.mm"
)
ALPHA_RESOURCE = (
    HISTORICAL
    / "nominal_alpha97_capture_safe_hardened_replay_adapter_001"
    / "resource.json"
)
PREDECESSOR_RESOURCE = (
    HISTORICAL
    / "reusable_nominal_mm_translator_v3_chunk017_compact_001"
    / "resource.json"
)
REFERENCE_DIR = (
    HISTORICAL
    / "reusable_nominal_mm_translator_v3_chunk018_compact_001"
)

EXPECTED = {
    "NominalWPPReplayChunk018Compact001.lean":
        "D549ACE24BD40B5E4C8D422CCEC54AA128B41A85FF28393F0A54C43FA6C2F8EB",
    "NominalWPPReplayChunk018Compact001Part001.lean":
        "A9782A12DF7A3842C792E75C67835F3EE5345D35719E6CF9DD38AD000C472DE5",
    "NominalWPPReplayChunk018Compact001Part002.lean":
        "CDF3F363A81F2E7BA206B736282FD3C360B4D37F71259901F43873514972E615",
    "NominalWPPReplayChunk018Compact001Part003.lean":
        "5C09B85D3A13B2BDF59135F178B59E233BC825BA5508DB639793782F2B4FE97C",
    "NominalWPPReplayChunk018Compact001Part004.lean":
        "366D0667A8D38AD4CA6AB12C4A7094910E1B9E95241BAC7DABE2C11DD26C5277",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def verify_output(output_dir: Path) -> None:
    failures: list[str] = []
    for name, expected in EXPECTED.items():
        generated = output_dir / name
        reference = REFERENCE_DIR / name
        if not generated.is_file():
            failures.append(f"missing generated file: {generated}")
            continue
        actual = sha256(generated)
        if actual != expected:
            failures.append(f"hash mismatch for {name}: {actual}")
        if not reference.is_file() or generated.read_bytes() != reference.read_bytes():
            failures.append(f"historical byte comparison failed for {name}")
        proof_copy = REPO / "Proof" / name
        if not proof_copy.is_file() or generated.read_bytes() != proof_copy.read_bytes():
            failures.append(f"Proof/ byte comparison failed for {name}")
    if failures:
        raise RuntimeError("\n".join(failures))
    print(f"PASS: all {len(EXPECTED)} C18 Lean files are byte-identical")


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Regenerate C18 with the portable, hash-checked translator"
    )
    parser.add_argument("output_dir", type=Path)
    parser.add_argument(
        "--verify-only",
        action="store_true",
        help="check an existing output directory without translating",
    )
    return parser


def main() -> int:
    args = make_parser().parse_args()
    output_dir = args.output_dir.resolve()
    if args.verify_only:
        verify_output(output_dir)
        return 0
    if output_dir.exists():
        raise RuntimeError(f"refusing to overwrite existing output: {output_dir}")
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    translator_args = [
        "--source", str(SOURCE),
        "--source-sha256",
        "868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F",
        "--endpoint", "wppfiniteblocknotwppndv",
        "--start-ordinal", "4255",
        "--end-ordinal", "4321",
        "--alpha-frontier-resource", str(ALPHA_RESOURCE),
        "--alpha-frontier-sha256",
        "0734B024E79B16AF57BB4EB5265E6E22FF9F9F9598B6CB0210837E221EBE6353",
        "--output-dir", str(output_dir),
        "--split-bytes", "60000",
        "--predecessor-resource", str(PREDECESSOR_RESOURCE),
        "--predecessor-resource-sha256",
        "86C7314D0BEB6A78F72DAE5BB871362883C5099492314F3DC8915E4E545EE3AD",
        "--module-prefix", "NominalWPPReplayChunk018Compact001",
        "--namespace", "NFChoice.DirectNominalPrf.WPPReplay",
        "--wpp-profile", "WPP_PROFILE_V2",
    ]
    status = portable.main(translator_args)
    if status != 0:
        return status
    verify_output(output_dir)
    print(f"receipts: {output_dir / 'resource.json'}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RuntimeError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
