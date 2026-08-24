#!/usr/bin/env python3
"""Create a flattened audit copy with two accidental global DV leaks scoped.

The transformation is deliberately surgical.  It wraps the historical
``$d c e R A $.`` declaration around the two assertions that need it, and the
historical ``$d v A $.`` declaration around its one assertion.  The original
assertion labels, expressions, and proof token streams are not modified.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
SOURCE = (
    WORKSPACE
    / "work/formalization_continue/cumulative_finite_block"
    / "common_ambient_hartogs_graph/flattening_audit"
    / "wppfiniteblocknotwpp_flattened_test.mm"
)
OUTPUT = HERE / "wppfiniteblocknotwpp_mm0_dv_clean.mm"
REPORT = HERE / "wppfiniteblocknotwpp_mm0_dv_clean.audit.json"
SOURCE_SHA256 = "DD1E4E778EB2B023827AF2AFFB35E043482B538118CFFB1932BFA7642C00C751"


def sha256_bytes(data: bytes) -> str:
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


def structural_spans(text: str):
    tokens = tokens_with_spans(text)
    depth = 1
    assertions: dict[str, tuple[int, int, str, int, tuple[str, ...]]] = {}
    top_dvs: list[tuple[tuple[str, ...], int, int]] = []
    index = 0
    while index < len(tokens):
        token, start, end = tokens[index]
        if token == "${":
            depth += 1
            index += 1
            continue
        if token == "$}":
            depth -= 1
            index += 1
            continue
        if token == "$d":
            values: list[str] = []
            cursor = index + 1
            while tokens[cursor][0] != "$.":
                values.append(tokens[cursor][0])
                cursor += 1
            if depth == 1:
                top_dvs.append((tuple(values), start, tokens[cursor][2]))
            index = cursor + 1
            continue
        if index + 1 < len(tokens) and tokens[index + 1][0] in {"$a", "$p"}:
            label = token
            kind = tokens[index + 1][0]
            cursor = index + 2
            expression: list[str] = []
            while tokens[cursor][0] not in {"$=", "$."}:
                expression.append(tokens[cursor][0])
                cursor += 1
            while tokens[cursor][0] != "$.":
                cursor += 1
            assertions[label] = (
                start,
                tokens[cursor][2],
                kind,
                depth,
                tuple(expression),
            )
            index = cursor + 1
            continue
        index += 1
    if depth != 1:
        raise ValueError(f"unbalanced Metamath scopes: final depth {depth}")
    return assertions, top_dvs


def main() -> None:
    raw = SOURCE.read_bytes()
    actual_sha = sha256_bytes(raw)
    if actual_sha != SOURCE_SHA256:
        raise ValueError(f"pinned source hash mismatch: {actual_sha}")
    text = raw.decode("utf-8")
    assertions, top_dvs = structural_spans(text)

    first = [item for item in top_dvs if item[0] == ("c", "e", "R", "A")]
    second = [item for item in top_dvs if item[0] == ("v", "A")]
    if len(first) != 1 or len(second) != 1:
        raise ValueError(f"unexpected target DV declarations: {first!r}, {second!r}")

    first_start = first[0][1]
    first_end = assertions["wppstrictleastbridge"][1]
    second_start = second[0][1]
    second_end = assertions["hncodecutreledgeihwcn"][1]
    for label in ("wppstrictcomplement", "wppstrictleastbridge", "hncodecutreledgeihwcn"):
        if assertions[label][3] != 1:
            raise ValueError(f"expected top-level assertion: {label}")
    if not (first_start < first_end < second_start < second_end):
        raise ValueError("unexpected source ordering for scoped DV repairs")

    insertions: dict[int, list[str]] = {
        first_start: ["${\n"],
        first_end: ["\n$}"],
        second_start: ["${\n"],
        second_end: ["\n$}"],
    }
    pieces: list[str] = []
    cursor = 0
    for position in sorted(insertions):
        pieces.append(text[cursor:position])
        pieces.extend(insertions[position])
        cursor = position
    pieces.append(text[cursor:])
    scoped_text = "".join(pieces)

    # Preserve the original global-DV proof environment and every non-syntax
    # assertion's mandatory-DV contract.  Each later assertion receives the
    # old global declarations in a private scope; syntax declarations are the
    # sole intentional exception.
    scoped_assertions, _ = structural_spans(scoped_text)
    first_boundary = scoped_assertions["wppstrictleastbridge"][1]
    second_boundary = scoped_assertions["hncodecutreledgeihwcn"][1]
    wrappers: dict[int, list[str]] = {}
    wrapped_first = 0
    wrapped_second = 0
    for label, (start, end, kind, _depth, expression) in scoped_assertions.items():
        is_syntax = kind == "$a" and expression and expression[0] in {
            "wff",
            "class",
            "setvar",
        }
        declarations: list[str] = []
        if start > first_boundary and not is_syntax:
            declarations.append("  $d c e R A $.\n")
            wrapped_first += 1
        if start > second_boundary and not is_syntax:
            declarations.append("  $d v A $.\n")
            wrapped_second += 1
        if declarations:
            wrappers.setdefault(start, []).append("${\n" + "".join(declarations))
            wrappers.setdefault(end, []).append("\n$}")

    pieces = []
    cursor = 0
    for position in sorted(wrappers):
        pieces.append(scoped_text[cursor:position])
        # At a shared end/start boundary, close prior assertion scopes first.
        pieces.extend(sorted(wrappers[position], key=lambda value: value.startswith("${")))
        cursor = position
    pieces.append(scoped_text[cursor:])
    output_text = "".join(pieces)
    OUTPUT.write_text(output_text, encoding="utf-8", newline="\n")

    report = {
        "source": str(SOURCE),
        "source_bytes": len(raw),
        "source_sha256": actual_sha,
        "output": str(OUTPUT),
        "output_bytes": OUTPUT.stat().st_size,
        "output_sha256": sha256_bytes(OUTPUT.read_bytes()),
        "transformation": [
            "scope $d c e R A $. through wppstrictleastbridge",
            "scope $d v A $. through hncodecutreledgeihwcn",
            "restore old global DV environments privately on every later non-syntax assertion",
        ],
        "assertions_privately_scoped_for_c_e_R_A": wrapped_first,
        "assertions_privately_scoped_for_v_A": wrapped_second,
        "assertion_or_proof_tokens_rewritten": 0,
        "j_metadata_blocks_before": text.count("$( $j"),
        "j_metadata_blocks_after": output_text.count("$( $j"),
    }
    REPORT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
