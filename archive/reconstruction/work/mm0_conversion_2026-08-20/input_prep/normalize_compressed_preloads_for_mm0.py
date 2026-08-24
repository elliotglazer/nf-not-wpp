#!/usr/bin/env python3
"""Normalize compressed Metamath proof preloads for the MM0 importer.

The Metamath compressed-proof table already contains every mandatory
hypothesis implicitly.  Some generated proofs redundantly list mandatory
``$e`` hypotheses in the parenthesized *extra-label* list.  Metamath accepts
that redundancy, but ``mm0-hs from-mm`` deliberately rejects every ``$e`` in
the extra-label list.

This script removes only explicit labels that already occur in the theorem's
implicit mandatory-hypothesis table, then renumbers label and saved-subproof
references.  It does not expand or otherwise alter the proof DAG.

Usage:
  python normalize_compressed_preloads_for_mm0.py INPUT.mm OUTPUT.mm
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
VERIFY = (
    WORKSPACE
    / "work/formalization_continue/release_final_2026-08-17"
    / "formalization_continue/reconstruct/mmverify_simple.py"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def load_database(source: Path):
    spec = importlib.util.spec_from_file_location("mm0_preload_db", VERIFY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import verifier: {VERIFY}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    db = module.load_database(source, allow_unknown=False, verify_proofs=True)
    return module, db


def tokens_with_spans(text: str) -> list[tuple[str, int, int]]:
    out: list[tuple[str, int, int]] = []
    i = 0
    while i < len(text):
        if text.startswith("$(", i):
            end = text.find("$)", i + 2)
            if end < 0:
                raise ValueError("unterminated Metamath comment")
            i = end + 2
            continue
        if text[i].isspace():
            i += 1
            continue
        start = i
        while i < len(text) and not text[i].isspace():
            if i > start and text.startswith("$(", i):
                break
            i += 1
        out.append((text[start:i], start, i))
    return out


def encode_number(number_zero_based: int) -> str:
    number = number_zero_based + 1
    quotient, final = divmod(number - 1, 20)
    digits: list[str] = []
    while quotient:
        quotient, digit = divmod(quotient - 1, 5)
        digits.append(chr(ord("U") + digit))
    return "".join(reversed(digits)) + chr(ord("A") + final)


def normalize_proof(db, statement, proof: list[str]):
    if not proof or proof[0] != "(":
        return None
    close = proof.index(")")
    mandatory = list(statement.hyps)
    old_extras = proof[1:close]
    old_labels = mandatory + old_extras

    # Preserve every genuine extra in its original position.  Only redundant
    # mandatory labels are removed; this keeps the edit surface minimal.
    new_extras = [label for label in old_extras if label not in mandatory]
    if new_extras == old_extras:
        return None
    new_labels = mandatory + new_extras
    new_index: dict[str, int] = {}
    for i, label in enumerate(new_labels):
        new_index.setdefault(label, i)

    _labels, sequence = db._decode_compressed(proof, statement)
    encoded: list[str] = []
    for item in sequence:
        if item == -1:
            encoded.append("Z")
        elif item < len(old_labels):
            encoded.append(encode_number(new_index[old_labels[item]]))
        else:
            saved_index = item - len(old_labels)
            encoded.append(encode_number(len(new_labels) + saved_index))
    return (
        ["(", *new_extras, ")", "".join(encoded)],
        [label for label in old_extras if label in mandatory],
    )


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    source = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2]).resolve()
    _module, db = load_database(source)
    text = source.read_text(encoding="utf-8")
    spans = tokens_with_spans(text)
    replacements: list[tuple[int, int, str]] = []
    changes: list[dict[str, object]] = []

    i = 0
    while i + 1 < len(spans):
        label, _, _ = spans[i]
        if spans[i + 1][0] != "$p":
            i += 1
            continue
        cursor = i + 2
        while spans[cursor][0] != "$=":
            cursor += 1
        first = cursor + 1
        end = first
        while spans[end][0] != "$.":
            end += 1
        proof = [token for token, _, _ in spans[first:end]]
        statement = db.labels[label]
        result = normalize_proof(db, statement, proof)
        if result is not None:
            new_tokens, removed = result
            replacement = " ".join(new_tokens) + " "
            replacements.append((spans[first][1], spans[end][1], replacement))
            changes.append(
                {
                    "label": label,
                    "removed_redundant_mandatory_preloads": removed,
                    "old_proof_token_count": len(proof),
                    "new_proof_token_count": len(new_tokens),
                }
            )
        i = end + 1

    pieces: list[str] = []
    cursor = 0
    for start, end, replacement in replacements:
        pieces.append(text[cursor:start])
        pieces.append(replacement)
        cursor = end
    pieces.append(text[cursor:])
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("".join(pieces), encoding="utf-8", newline="\n")

    report = {
        "source": str(source),
        "source_sha256": sha256(source),
        "output": str(output),
        "output_sha256": sha256(output),
        "changed_proof_count": len(changes),
        "changes": changes,
        "assertion_or_hypothesis_tokens_changed": 0,
    }
    report_path = output.with_suffix(".preload_normalization.json")
    report_path.write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
