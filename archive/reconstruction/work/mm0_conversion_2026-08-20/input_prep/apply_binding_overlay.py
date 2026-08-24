#!/usr/bin/env python3
"""Append the pinned MM0 binding metadata overlay to the compressed input."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
SOURCE = HERE / "wppfiniteblocknotwpp_mm0_compressed.mm"
OVERLAY = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/metadata_audit"
    / "proposed_binding_overlay.mm.inc"
)
OUTPUT = HERE / "wppfiniteblocknotwpp_mm0_input.mm"
REPORT = HERE / "wppfiniteblocknotwpp_mm0_input.overlay.audit.json"
OVERLAY_SHA256 = "6FD0E6E2AF6EE098B11635C756E49D459EACEC408F930D6368BA98AF867F0FAA"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def main() -> None:
    source = SOURCE.read_bytes()
    overlay = OVERLAY.read_bytes()
    overlay_sha = sha256(overlay)
    if overlay_sha != OVERLAY_SHA256:
        raise ValueError(f"binding overlay hash mismatch: {overlay_sha}")
    if b"free_var 'weq'" in overlay or b"free_var 'wel'" in overlay:
        raise ValueError("proof-syntax weq/wel must not be constructor metadata")
    if not source.endswith(b"\n"):
        source += b"\n"
    output = source + b"\n" + overlay
    if not output.endswith(b"\n"):
        output += b"\n"
    OUTPUT.write_bytes(output)
    report = {
        "source": str(SOURCE),
        "source_bytes": len(source),
        "source_sha256": sha256(source),
        "overlay": str(OVERLAY),
        "overlay_bytes": len(overlay),
        "overlay_sha256": overlay_sha,
        "output": str(OUTPUT),
        "output_bytes": len(output),
        "output_sha256": sha256(output),
        "overlay_is_comment_only": overlay.lstrip().startswith(b"$(")
        and overlay.rstrip().endswith(b"$)"),
        "original_j_metadata_blocks": source.count(b"$( $j"),
        "output_j_metadata_blocks": output.count(b"$( $j"),
        "metamath_tokens_changed_by_overlay": 0,
    }
    REPORT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
