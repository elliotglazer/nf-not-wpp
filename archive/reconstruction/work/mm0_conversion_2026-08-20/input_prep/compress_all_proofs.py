#!/usr/bin/env python3
"""Deterministically compress every normal proof in the DV-clean audit copy."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
SOURCE = HERE / "wppfiniteblocknotwpp_mm0_dv_clean.mm"
OUTPUT = HERE / "wppfiniteblocknotwpp_mm0_compressed.mm"
REPORT = HERE / "wppfiniteblocknotwpp_mm0_compressed.audit.json"
VERIFY = (
    WORKSPACE
    / "work/formalization_continue/root_integration/local_mm_verify_compressed.py"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def tokens_with_spans(text: str) -> list[tuple[str, int, int]]:
    out: list[tuple[str, int, int]] = []
    index = 0
    while index < len(text):
        if text.startswith("$(", index):
            end = text.find("$)", index + 2)
            if end < 0:
                raise ValueError("unterminated Metamath comment")
            index = end + 2
            continue
        if text[index].isspace():
            index += 1
            continue
        start = index
        while index < len(text) and not text[index].isspace():
            if index > start and text.startswith("$(", index):
                break
            index += 1
        out.append((text[start:index], start, index))
    return out


def load_database(source: Path):
    spec = importlib.util.spec_from_file_location("mm0_compression_verifier", VERIFY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import verifier: {VERIFY}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    checker = module.MM(WORKSPACE / "work/formalization_continue")
    checker.process(source)
    if checker.trusted:
        raise ValueError(f"unexpected trusted proofs: {checker.trusted!r}")
    return checker


def encode_number(number: int) -> str:
    quotient, final = divmod(number - 1, 20)
    digits: list[str] = []
    while quotient:
        quotient, digit = divmod(quotient - 1, 5)
        digits.append(chr(ord("U") + digit))
    return "".join(reversed(digits)) + chr(ord("A") + final)


def compressed_proof(mandatory: list[str], proof: list[str]) -> str:
    extras: list[str] = []
    for label in proof:
        if label not in mandatory and label not in extras:
            extras.append(label)
    table = mandatory + extras
    indices = {label: index + 1 for index, label in enumerate(table)}
    return "( " + " ".join(extras) + " ) " + "".join(
        encode_number(indices[label]) for label in proof
    )


def main() -> None:
    raw = SOURCE.read_bytes()
    text = raw.decode("utf-8")
    checker = load_database(SOURCE)
    tokens = tokens_with_spans(text)
    replacements: list[tuple[int, int, str, str]] = []
    proof_count = 0
    already_compressed = 0
    index = 0
    while index < len(tokens):
        if index + 1 >= len(tokens) or tokens[index + 1][0] != "$p":
            index += 1
            continue
        label = tokens[index][0]
        cursor = index + 2
        while tokens[cursor][0] != "$=":
            if tokens[cursor][0] == "$.":
                raise ValueError(f"missing proof for {label}")
            cursor += 1
        proof_first = cursor + 1
        proof_end = proof_first
        while tokens[proof_end][0] != "$.":
            proof_end += 1
        proof_tokens = [token for token, _, _ in tokens[proof_first:proof_end]]
        if not proof_tokens or "?" in proof_tokens:
            raise ValueError(f"incomplete proof for {label}")
        proof_count += 1
        if proof_tokens[0] == "(":
            already_compressed += 1
        else:
            mandatory = [hyp_label for hyp_label, _ in checker.labels[label].hyps]
            replacement = compressed_proof(mandatory, proof_tokens)
            replacements.append(
                (
                    tokens[proof_first][1],
                    tokens[proof_end][1],
                    replacement + " ",
                    label,
                )
            )
        index = proof_end + 1

    pieces: list[str] = []
    cursor = 0
    for start, end, replacement, _label in replacements:
        pieces.append(text[cursor:start])
        pieces.append(replacement)
        cursor = end
    pieces.append(text[cursor:])
    output_text = "".join(pieces)
    OUTPUT.write_text(output_text, encoding="utf-8", newline="\n")

    report = {
        "source": str(SOURCE),
        "source_bytes": len(raw),
        "source_sha256": sha256(raw),
        "output": str(OUTPUT),
        "output_bytes": OUTPUT.stat().st_size,
        "output_sha256": sha256(OUTPUT.read_bytes()),
        "proofs_total": proof_count,
        "proofs_already_compressed": already_compressed,
        "normal_proofs_converted": len(replacements),
        "assertion_expressions_rewritten": 0,
        "j_metadata_blocks_before": text.count("$( $j"),
        "j_metadata_blocks_after": output_text.count("$( $j"),
    }
    REPORT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
