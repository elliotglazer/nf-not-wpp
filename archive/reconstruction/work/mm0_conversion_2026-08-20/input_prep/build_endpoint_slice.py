#!/usr/bin/env python3
"""Build a token-faithful endpoint slice by blanking unrelated $p statements."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
DEFAULT_SOURCE = HERE / "wppfiniteblocknotwpp_mm0_input.mm"
DEFAULT_OUTPUT = HERE / "wppfiniteblocknotwpp_mm0_endpoint_slice.mm"
VERIFY = WORKSPACE / "work/formalization_continue/root_integration/local_mm_verify_compressed.py"
ENDPOINT = "wppfiniteblocknotwppndv"


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


def decode_indices(parts: list[str]) -> set[int]:
    result: set[int] = set()
    acc = 0
    for char in "".join(parts):
        if "U" <= char <= "Y":
            acc = 5 * acc + ord(char) - ord("U") + 1
        elif "A" <= char <= "T":
            result.add(20 * acc + ord(char) - ord("A") + 1)
            acc = 0
        elif char in "Z?":
            if acc:
                raise ValueError("unfinished compressed integer")
        else:
            raise ValueError(f"bad compressed character {char!r}")
    if acc:
        raise ValueError("unfinished compressed integer at EOF")
    return result


def load_database(source: Path):
    spec = importlib.util.spec_from_file_location("endpoint_slice_verifier", VERIFY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import verifier: {VERIFY}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    checker = module.MM(WORKSPACE / "work/formalization_continue")
    checker.process(source)
    return checker


def statement_hash(parts: list[str]) -> str:
    return sha("\0".join(parts).encode("utf-8"))


def main() -> None:
    if len(sys.argv) not in {1, 2}:
        raise SystemExit("usage: build_endpoint_slice.py [SOURCE.mm]")
    source = DEFAULT_SOURCE if len(sys.argv) == 1 else Path(sys.argv[1]).resolve()
    output = DEFAULT_OUTPUT if len(sys.argv) == 1 else source.with_name(source.stem + "_endpoint_slice.mm")
    report_path = output.with_suffix(".audit.json")
    source_bytes = source.read_bytes()
    text = source_bytes.decode("utf-8")
    checker = load_database(source)
    kinds = {label: assertion.kind for label, assertion in checker.labels.items()}
    toks = tokens_with_spans(text)
    p_spans: dict[str, tuple[int, int]] = {}
    p_tokens: dict[str, list[str]] = {}
    parser_dependencies: dict[str, set[str]] = {}
    semantic_dependencies: dict[str, set[str]] = {}

    i = 0
    while i < len(toks):
        if i + 1 >= len(toks) or toks[i + 1][0] != "$p":
            i += 1
            continue
        label = toks[i][0]
        start = toks[i][1]
        cursor = i + 2
        while toks[cursor][0] != "$=":
            cursor += 1
        proof_start = cursor + 1
        proof_end = proof_start
        while toks[proof_end][0] != "$.":
            proof_end += 1
        end = toks[proof_end][2]
        statement = [item[0] for item in toks[i : proof_end + 1]]
        proof = [item[0] for item in toks[proof_start:proof_end]]
        p_spans[label] = (start, end)
        p_tokens[label] = statement
        if proof and proof[0] == "(":
            close = proof.index(")")
            preload = proof[1:close]
            mandatory = len(checker.labels[label].hyps)
            used = decode_indices(proof[close + 1 :])
            parser_dependencies[label] = {
                dep for dep in preload if kinds.get(dep) == "$p"
            }
            semantic_dependencies[label] = {
                dep
                for offset, dep in enumerate(preload, 1)
                if kinds.get(dep) == "$p" and mandatory + offset in used
            }
        else:
            deps = {dep for dep in proof if kinds.get(dep) == "$p"}
            parser_dependencies[label] = deps
            semantic_dependencies[label] = deps
        i = proof_end + 1

    j_text = "\n".join(
        match.group(1)
        for match in re.finditer(r"\$\((.*?)\$\)", text, flags=re.DOTALL)
        if re.match(r"\s*\$j(?:\s|$)", match.group(1))
    )
    j_words = set(re.findall(r"[A-Za-z0-9_.-]+", j_text))
    metadata_roots = sorted(label for label in p_spans if label in j_words)
    roots = [ENDPOINT, *metadata_roots]

    retained: set[str] = set()
    todo = list(roots)
    while todo:
        theorem = todo.pop()
        if theorem in retained:
            continue
        if theorem not in p_spans:
            raise ValueError(f"root/dependency is not a $p statement: {theorem}")
        retained.add(theorem)
        todo.extend(parser_dependencies[theorem] - retained)

    removed = sorted(set(p_spans) - retained)
    comments_inside_removed = [
        label
        for label in removed
        if "$(" in text[p_spans[label][0] : p_spans[label][1]]
    ]
    if comments_inside_removed:
        raise ValueError(
            f"cannot preserve comments while blanking statements: {comments_inside_removed[:5]}"
        )
    chars = list(text)
    for label in removed:
        start, end = p_spans[label]
        for pos in range(start, end):
            if chars[pos] not in "\r\n":
                chars[pos] = " "
    output_text = "".join(chars)
    output.write_text(output_text, encoding="utf-8", newline="")

    output_toks = tokens_with_spans(output_text)
    output_p_tokens: dict[str, list[str]] = {}
    i = 0
    while i < len(output_toks):
        if i + 1 >= len(output_toks) or output_toks[i + 1][0] != "$p":
            i += 1
            continue
        label = output_toks[i][0]
        end = i + 2
        while output_toks[end][0] != "$.":
            end += 1
        output_p_tokens[label] = [item[0] for item in output_toks[i : end + 1]]
        i = end + 1

    if set(output_p_tokens) != retained:
        raise ValueError("retained theorem label set changed during slicing")
    mismatches = [
        label for label in retained if output_p_tokens[label] != p_tokens[label]
    ]
    if mismatches:
        raise ValueError(f"retained theorem token mismatch: {mismatches[:5]}")
    dangling = sorted(
        (theorem, dep)
        for theorem in retained
        for dep in parser_dependencies[theorem]
        if dep not in retained
    )
    if dangling:
        raise ValueError(f"dangling parser dependency: {dangling[:5]}")

    semantic: set[str] = set()
    todo = [ENDPOINT]
    while todo:
        theorem = todo.pop()
        if theorem in semantic:
            continue
        semantic.add(theorem)
        todo.extend(semantic_dependencies[theorem] - semantic)

    report = {
        "status": "PASS",
        "source": str(source),
        "source_bytes": len(source_bytes),
        "source_sha256": sha(source_bytes),
        "output": str(output),
        "output_bytes": output.stat().st_size,
        "output_sha256": sha(output.read_bytes()),
        "endpoint": ENDPOINT,
        "metadata_p_roots": metadata_roots,
        "proofs_source": len(p_spans),
        "proofs_retained": len(retained),
        "proofs_removed": len(removed),
        "retained_theorem_assertion_and_proof_tokens_identical": not mismatches,
        "retained_theorem_token_hashes": {
            label: statement_hash(p_tokens[label]) for label in sorted(retained)
        },
        "endpoint_statement_token_sha256": statement_hash(p_tokens[ENDPOINT]),
        "all_explicit_p_preloads_resolve": not dangling,
        "comments_and_non_p_statements_byte_position_preserved": True,
        "removed_p_labels": removed,
        "semantic_endpoint_dependency_closure_size": len(semantic),
        "parser_retention_closure_size": len(retained),
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({key: value for key, value in report.items() if key not in {
        "retained_theorem_token_hashes", "removed_p_labels"
    }}, indent=2))


if __name__ == "__main__":
    main()
