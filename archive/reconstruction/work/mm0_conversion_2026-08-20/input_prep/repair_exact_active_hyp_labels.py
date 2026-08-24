#!/usr/bin/env python3
"""Replace only inactive $e preload labels with exact active-formula hypotheses."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
SOURCE = HERE / "wppfiniteblocknotwpp_mm0_input.mm"
AUDIT = SOURCE.with_suffix(".ehyp_preload_audit.json")
OUTPUT = HERE / "wppfiniteblocknotwpp_mm0_hyp_label_repaired22.mm"
MANIFEST = HERE / "wppfiniteblocknotwpp_mm0_hyp_label_repaired22.manifest.json"
VERIFY = WORKSPACE / "work/formalization_continue/root_integration/local_mm_verify_compressed.py"
EXPECTED_SOURCE_SHA256 = "F7A8B4B332489EF4657DACFA8E633E581A7F4D99750F77EA5BA4D62157789036"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def tokens_with_spans(text: str) -> list[tuple[str, int, int]]:
    result: list[tuple[str, int, int]] = []
    i = 0
    while i < len(text):
        if text.startswith("$(", i):
            end = text.find("$)", i + 2)
            if end < 0:
                raise ValueError("unterminated comment")
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
        result.append((text[start:i], start, i))
    return result


def load_database(source: Path):
    spec = importlib.util.spec_from_file_location("hyp_repair_verifier", VERIFY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import verifier: {VERIFY}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    checker = module.MM(WORKSPACE / "work/formalization_continue")
    checker.process(source)
    return checker


def formula_sha(expr: tuple[str, ...]) -> str:
    return sha("\0".join(expr).encode("utf-8"))


def main() -> None:
    if len(sys.argv) != 1:
        raise SystemExit("usage: repair_exact_active_hyp_labels.py")
    source_bytes = SOURCE.read_bytes()
    if sha(source_bytes) != EXPECTED_SOURCE_SHA256:
        raise ValueError("source hash differs from the pinned converter input")
    text = source_bytes.decode("utf-8")
    audit = json.loads(AUDIT.read_text(encoding="utf-8"))
    requested = {
        (item["theorem"], item["essential_preload"]): item["exact_replacement_label"]
        for item in audit["essential_preload_occurrence_records"]
        if item["exact_replacement_label"] is not None
    }
    if len(requested) != 22:
        raise ValueError(f"expected 22 exact replacements, found {len(requested)}")
    checker = load_database(SOURCE)
    toks = tokens_with_spans(text)
    replacements: list[tuple[int, int, str, str, str]] = []
    i = 0
    while i < len(toks):
        if i + 1 >= len(toks) or toks[i + 1][0] != "$p":
            i += 1
            continue
        theorem = toks[i][0]
        cursor = i + 2
        while toks[cursor][0] != "$=":
            cursor += 1
        proof = cursor + 1
        if toks[proof][0] != "(":
            while toks[proof][0] != "$.":
                proof += 1
            i = proof + 1
            continue
        proof += 1
        while toks[proof][0] != ")":
            old, start, end = toks[proof]
            new = requested.get((theorem, old))
            if new is not None:
                old_expr = checker.labels[old].expr
                new_expr = checker.labels[new].expr
                if old_expr != new_expr:
                    raise ValueError(f"formula mismatch for {theorem}: {old} -> {new}")
                replacements.append((start, end, new, theorem, old))
            proof += 1
        while toks[proof][0] != "$.":
            proof += 1
        i = proof + 1

    found = {(theorem, old): new for _, _, new, theorem, old in replacements}
    if found != requested or len(replacements) != 22:
        raise ValueError("source replacement sites do not match the strict audit")

    pieces: list[str] = []
    cursor = 0
    manifest_rows: list[dict[str, object]] = []
    for start, end, new, theorem, old in replacements:
        pieces.append(text[cursor:start])
        pieces.append(new)
        cursor = end
        expr = checker.labels[old].expr
        manifest_rows.append(
            {
                "theorem": theorem,
                "old_inactive_hypothesis_label": old,
                "new_active_identical_formula_label": new,
                "source_character_start": start,
                "source_character_end": end,
                "formula_tokens": list(expr),
                "formula_token_sha256": formula_sha(expr),
            }
        )
    pieces.append(text[cursor:])
    output_text = "".join(pieces)
    OUTPUT.write_text(output_text, encoding="utf-8", newline="")

    # Assertions and encoded proof letters are byte-for-token identical.  Only the
    # 22 named labels in compressed parenthesis lists differ.
    manifest = {
        "status": "PASS",
        "source": str(SOURCE),
        "source_bytes": len(source_bytes),
        "source_sha256": sha(source_bytes),
        "strict_audit": str(AUDIT),
        "strict_audit_sha256": sha(AUDIT.read_bytes()),
        "output": str(OUTPUT),
        "output_bytes": OUTPUT.stat().st_size,
        "output_sha256": sha(OUTPUT.read_bytes()),
        "replacement_count": len(manifest_rows),
        "replacement_rule": "inactive explicit $e preload -> unique active $e with byte-identical formula tokens",
        "assertion_tokens_changed": 0,
        "compressed_proof_code_tokens_changed": 0,
        "other_parenthesis_labels_changed": 0,
        "replacements": manifest_rows,
    }
    MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({key: value for key, value in manifest.items() if key != "replacements"}, indent=2))


if __name__ == "__main__":
    main()
