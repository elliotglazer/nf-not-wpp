#!/usr/bin/env python3
"""Merge independently repaired Metamath proof bodies onto one audited parent.

Usage:
  python merge_scope_repair_proofs.py BASE.mm OUTPUT.mm LABEL=DONOR.mm [...]

Only the compressed proof body between ``$=`` and ``$.`` is copied.  The
statement prefix (label, kind, assertion, and hypotheses in force) must be
token-identical in the base and donor.  A JSON manifest is written next to the
output so that the merge can be audited before any converter is run.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def theorem_pattern(label: str) -> re.Pattern[str]:
    return re.compile(
        r"(?P<head>\b" + re.escape(label)
        + r"\s+\$p\s+.*?\s+\$=)(?P<proof>.*?)(?P<end>\s+\$\.)",
        re.S,
    )


def unique_match(text: str, label: str) -> re.Match[str]:
    matches = list(theorem_pattern(label).finditer(text))
    if len(matches) != 1:
        raise RuntimeError(f"expected one theorem {label}, found {len(matches)}")
    return matches[0]


def tokens(text: str) -> tuple[str, ...]:
    # Statement heads contain no comments in the generated audit source.  The
    # token comparison deliberately ignores only whitespace.
    return tuple(text.split())


def main() -> None:
    if len(sys.argv) < 4:
        raise SystemExit(__doc__)

    base = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2]).resolve()
    specs: list[tuple[str, Path]] = []
    for arg in sys.argv[3:]:
        if "=" not in arg:
            raise SystemExit(f"expected LABEL=DONOR.mm, got {arg!r}")
        label, donor = arg.split("=", 1)
        specs.append((label, Path(donor).resolve()))

    base_text = base.read_text(encoding="utf-8")
    merged = base_text
    changes: list[dict[str, object]] = []
    seen: set[str] = set()

    for label, donor in specs:
        if label in seen:
            raise RuntimeError(f"duplicate merge label {label}")
        seen.add(label)
        donor_text = donor.read_text(encoding="utf-8")
        bm = unique_match(merged, label)
        dm = unique_match(donor_text, label)
        if tokens(bm.group("head")) != tokens(dm.group("head")):
            raise RuntimeError(f"assertion head changed for {label}")
        old_proof = bm.group("proof")
        new_proof = dm.group("proof")
        if "$= ? $." in dm.group(0) or "?" in tokens(new_proof):
            raise RuntimeError(f"donor proof is incomplete for {label}")
        merged = merged[: bm.start("proof")] + new_proof + merged[bm.end("proof") :]
        changes.append(
            {
                "label": label,
                "donor": str(donor),
                "donor_sha256": sha256(donor),
                "old_proof_token_count": len(tokens(old_proof)),
                "new_proof_token_count": len(tokens(new_proof)),
                "proof_changed": tokens(old_proof) != tokens(new_proof),
            }
        )

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(merged, encoding="utf-8", newline="\n")
    manifest = {
        "base": str(base),
        "base_sha256": sha256(base),
        "output": str(output),
        "output_sha256": sha256(output),
        "changes": changes,
    }
    manifest_path = output.with_suffix(".merge.json")
    manifest_path.write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
