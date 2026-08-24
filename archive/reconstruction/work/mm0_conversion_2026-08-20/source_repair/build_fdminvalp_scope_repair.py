#!/usr/bin/env python3
"""Repair the hidden sethood premise in the FDMinValP membership proof.

This script works only on the quarantined MM0 audit input.  It adds the
sethood premise actually consumed by ``fdminvalpbr`` and regenerates the five
proofs whose normal-form derivations inline that theorem.  The published
comment-free Metamath file is never modified.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
DEFAULT_INPUT = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/input_prep/"
    "wppfiniteblocknotwpp_mm0_input.mm"
)
INPUT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else DEFAULT_INPUT
OUTPUT = (
    Path(sys.argv[2]).resolve()
    if len(sys.argv) > 2
    else HERE / "fdminvalp_scope_repair_compressed.mm"
)
INTERMEDIATE = OUTPUT.with_name(OUTPUT.stem + "_normal.mm")
REPORT = OUTPUT.with_suffix(".audit.json")
BUILDER = WORKSPACE / "formalization_continue/reconstruct/mmproof_builder_current.py"
STAGE14_BUILDER = WORKSPACE / "work/continued_v2/build_stage14_map.py"
STAGE16_BUILDER = WORKSPACE / "work/continued_v2/build_stage16_bounds.py"
VERIFY = (
    WORKSPACE
    / "work/formalization_continue/root_integration/local_mm_verify_compressed.py"
)

TARGETS = (
    "fdminvalpbr",
    "fdminqbr",
    "fdpivmap2ex",
    "fdpivrange2ex",
    "fdminvalpss",
    "elfdminvalp",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def load_builder_database(path: Path):
    spec = importlib.util.spec_from_file_location("fdmin_scope_builder", BUILDER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {BUILDER}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module, module.load(path, verify=True, allow_incomplete=True)


def theorem_pattern(label: str) -> re.Pattern[str]:
    return re.compile(
        r"(" + re.escape(label) + r"\s+\$p\s+.*?\$=)\s*.*?\s*\$\.",
        re.S,
    )


def hole_proof(text: str, label: str) -> str:
    text, count = theorem_pattern(label).subn(
        lambda match: match.group(1) + " ? $.", text, count=1
    )
    if count != 1:
        raise RuntimeError(f"could not hole {label}: {count}")
    return text


def install_normal_proof(text: str, label: str, proof: list[str]) -> str:
    marker = re.compile(
        r"(" + re.escape(label) + r"\s+\$p\s+.*?\$=)\s*\?\s*\$\.",
        re.S,
    )
    text, count = marker.subn(
        lambda match: match.group(1) + "\n    " + " ".join(proof) + " $.",
        text,
        count=1,
    )
    if count != 1:
        raise RuntimeError(f"could not install {label}: {count}")
    return text


def run_stage14(pre: Path) -> dict[str, list[str]]:
    source = STAGE14_BUILDER.read_text(encoding="utf-8")
    source = source.replace(
        "'/mnt/data/mmproof_builder_current.py'", repr(str(BUILDER))
    )
    source = source.replace(
        "pre=Path('/mnt/data/nf_wpp_stage14_map_pre.mm')",
        f"pre=Path({str(pre)!r})",
    )
    source = source.replace(
        "out=Path('/mnt/data/nf_wpp_stage14_map.mm')",
        f"out=Path({str(HERE / 'stage14_generated.mm')!r})",
    )
    source = source.replace("p_C=['kqrelbr.2']", "p_C=['fdminvalpbr.1']")
    old = (
        "p_valp,_=ap('fdminvalpbr',{'R':('R',),'A':('A',),'B':('B',),"
        "'C':('p',),'z':('z',)},[])"
    )
    new = old[:-3] + "[p_p])"
    if old not in source:
        raise RuntimeError("stage-14 fdminvalpbr application not found")
    source = source.replace(old, new, 1)
    # Retain the constructed proof objects but skip the original pre-file
    # installer, which expects every stage-14 theorem to be a hole.
    source = source.split("src=pre.read_text()", 1)[0]
    namespace = {"__name__": "fdmin_stage14_rebuild", "__file__": str(STAGE14_BUILDER)}
    exec(compile(source, str(STAGE14_BUILDER), "exec"), namespace)
    proofs = namespace["proofs"]
    return {label: list(proofs[label]) for label in TARGETS[:4]}


def run_stage16(pre: Path) -> list[str]:
    source = STAGE16_BUILDER.read_text(encoding="utf-8")
    source = source.replace(
        "'/mnt/data/mmproof_builder_current.py'", repr(str(BUILDER))
    )
    source = source.replace(
        "pre=Path('/mnt/data/nf_wpp_stage16_bounds_pre.mm')",
        f"pre=Path({str(pre)!r})",
    )
    source = source.replace(
        "p_vbr,_=ap('fdminvalpbr',{'R':('R',),'A':('A',),'B':('B',),"
        "'C':('C',),'z':('z',)},[])"
        ,
        "p_vbr,_=ap('fdminvalpbr',{'R':('R',),'A':('A',),'B':('B',),"
        "'C':('C',),'z':('z',)},[Cset])",
        1,
    )
    # The desired proof has been built before the installer loop.  Avoid
    # rewriting unrelated already-complete theorems in the full audit input.
    source = source.split("# Install proofs.", 1)[0]
    namespace = {"__name__": "fdmin_stage16_rebuild", "__file__": str(STAGE16_BUILDER)}
    exec(compile(source, str(STAGE16_BUILDER), "exec"), namespace)
    return list(namespace["P"]["fdminvalpss"])


def build_elfdminvalp(pre: Path) -> list[str]:
    module, database = load_builder_database(pre)
    builder = module.Builder(database)

    def ap(label, subst=None, essentials=None):
        return builder.apply(label, subst or {}, essentials or [])

    d = ("d",)
    c = ("C",)
    r = ("R",)
    a = ("A",)
    b = ("B",)
    value = ("FDMinValP", "(", "R", ",", "A", ",", "B", ",", "C", ")")
    minimum = ("FDMinSep", "(", "R", ",", "A", ",", "B", ")")
    relation = ("<<", "{", "d", "}", ",", "C", ">>", "e.") + minimum
    in_value = ("d", "e.") + value
    in_a = ("d", "e.", "A")
    conjunction = ("(",) + in_a + ("/\\",) + relation + (")",)
    sethood = ["elfdminvalp.1"]

    p_subset, _ = ap(
        "fdminvalpss", {"C": c, "R": r, "A": a, "B": b}, [sethood]
    )
    p_in_a, _ = ap("sseli", {"A": value, "B": a, "C": d}, [p_subset])
    p_bridge, _ = ap(
        "fdminvalpbr",
        {"z": d, "C": c, "R": r, "A": a, "B": b},
        [sethood],
    )
    p_forward, _ = ap(
        "jca",
        {"ph": in_value, "ps": in_a, "ch": relation},
        [p_in_a, ap("biimpi", {"ph": in_value, "ps": relation}, [p_bridge])[0]],
    )
    p_reverse, _ = ap(
        "syl",
        {"ph": conjunction, "ps": relation, "ch": in_value},
        [
            ap("simpr", {"ph": in_a, "ps": relation})[0],
            ap("biimpri", {"ph": in_value, "ps": relation}, [p_bridge])[0],
        ],
    )
    proof, expression = ap(
        "impbii", {"ph": in_value, "ps": conjunction}, [p_forward, p_reverse]
    )
    if tuple(expression) != database.stmts["elfdminvalp"].expr:
        raise RuntimeError((expression, database.stmts["elfdminvalp"].expr))
    return list(proof)


def load_checker(path: Path):
    spec = importlib.util.spec_from_file_location("fdmin_scope_checker", VERIFY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {VERIFY}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    checker = module.MM(WORKSPACE / "work/formalization_continue")
    checker.process(path)
    if checker.trusted:
        raise RuntimeError(f"unexpected trusted proofs: {checker.trusted!r}")
    return checker


def token_spans(text: str) -> list[tuple[str, int, int]]:
    out: list[tuple[str, int, int]] = []
    index = 0
    while index < len(text):
        if text.startswith("$(", index):
            end = text.find("$)", index + 2)
            if end < 0:
                raise ValueError("unterminated comment")
            index = end + 2
            continue
        if text[index].isspace():
            index += 1
            continue
        start = index
        while index < len(text) and not text[index].isspace():
            index += 1
        out.append((text[start:index], start, index))
    return out


def encode_number(number: int) -> str:
    quotient, final = divmod(number - 1, 20)
    prefix: list[str] = []
    while quotient:
        quotient, digit = divmod(quotient - 1, 5)
        prefix.append(chr(ord("U") + digit))
    return "".join(reversed(prefix)) + chr(ord("A") + final)


def compress_normal_proofs(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    checker = load_checker(path)
    tokens = token_spans(text)
    replacements: list[tuple[int, int, str]] = []
    index = 0
    while index < len(tokens):
        if index + 1 >= len(tokens) or tokens[index + 1][0] != "$p":
            index += 1
            continue
        label = tokens[index][0]
        cursor = index + 2
        while tokens[cursor][0] != "$=":
            cursor += 1
        start = cursor + 1
        end = start
        while tokens[end][0] != "$.":
            end += 1
        proof = [token for token, _, _ in tokens[start:end]]
        if proof and proof[0] != "(":
            mandatory = [hyp_label for hyp_label, _ in checker.labels[label].hyps]
            extras: list[str] = []
            for item in proof:
                if item not in mandatory and item not in extras:
                    extras.append(item)
            table = mandatory + extras
            numbers = {item: offset + 1 for offset, item in enumerate(table)}
            compressed = "( " + " ".join(extras) + " ) " + "".join(
                encode_number(numbers[item]) for item in proof
            )
            replacements.append((tokens[start][1], tokens[end][1], compressed + " "))
        index = end + 1
    pieces: list[str] = []
    cursor = 0
    for start, end, replacement in replacements:
        pieces.extend((text[cursor:start], replacement))
        cursor = end
    pieces.append(text[cursor:])
    OUTPUT.write_text("".join(pieces), encoding="utf-8", newline="\n")


def main() -> None:
    original = INPUT.read_text(encoding="utf-8")
    build_original = DEFAULT_INPUT.read_text(encoding="utf-8")
    needle = "${\n  $d z C R A B $.\n  fdminvalpbr $p"
    replacement = (
        "${\n  $d z C R A B $.\n"
        "  fdminvalpbr.1 $e |- C e. _V $.\n"
        "  fdminvalpbr $p"
    )
    if original.count(needle) != 1 or build_original.count(needle) != 1:
        raise RuntimeError("fdminvalpbr declaration site was not unique")

    # Generate the repaired proof sequences against the full preliminary
    # database, even when the requested output is the endpoint dependency
    # slice and therefore omits unused intermediate assertions.
    build_text = build_original.replace(needle, replacement, 1)
    for label in TARGETS:
        build_text = hole_proof(build_text, label)

    pre = HERE / "fdminvalp_scope_repair_pre.mm"
    pre.write_text(build_text, encoding="utf-8", newline="\n")
    stage14 = run_stage14(pre)
    for label, proof in stage14.items():
        build_text = install_normal_proof(build_text, label, proof)
    pre.write_text(build_text, encoding="utf-8", newline="\n")

    proofs = dict(stage14)
    proofs["fdminvalpss"] = run_stage16(pre)
    build_text = install_normal_proof(build_text, "fdminvalpss", proofs["fdminvalpss"])
    pre.write_text(build_text, encoding="utf-8", newline="\n")
    proofs["elfdminvalp"] = build_elfdminvalp(pre)

    text = original.replace(needle, replacement, 1)
    installed: list[str] = []
    for label in TARGETS:
        if re.search(r"^\s*" + re.escape(label) + r"\s+\$p\b", text, re.M):
            text = hole_proof(text, label)
            text = install_normal_proof(text, label, proofs[label])
            installed.append(label)
    INTERMEDIATE.write_text(text, encoding="utf-8", newline="\n")

    compress_normal_proofs(INTERMEDIATE)
    checker = load_checker(OUTPUT)
    report = {
        "source": str(INPUT),
        "source_sha256": sha256(INPUT),
        "output": str(OUTPUT),
        "output_sha256": sha256(OUTPUT),
        "verified_proofs": len(checker.verified),
        "trusted_proofs": len(checker.trusted),
        "new_essential": "fdminvalpbr.1 $e |- C e. _V $.",
        "regenerated_proofs": installed,
        "published_file_modified": False,
    }
    REPORT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
