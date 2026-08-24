#!/usr/bin/env python3
"""Flatten and structurally rebase the verified HNWCut helper tails.

The donor tails were checked in include-isolated contexts.  This builder puts
the same assertion blocks into the physical BE2D parent and re-emits each proof
DAG in the parent's mandatory-hypothesis order.
"""

from hashlib import sha256
from pathlib import Path
import gc
import importlib.util
import re
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PARENT = (
    ROOT / "work/mm0_conversion_2026-08-20/toolchain/hnwcut_factor_value_stage5"
    / "value_ambient_be2d_frozen_checkpoint.mm"
)
PARENT_SHA = "2BBB76DD71F34B66F0CBE74EB49E64C3F691766B01F6D208E0FA00EF375A8314"
F1 = ROOT / "work/mm0_conversion_2026-08-20/source_repair/hnwcut_alias/value_ambient_f1_be2d_live.mm"
RANGE = ROOT / "work/mm0_conversion_2026-08-20/source_repair/hnwcut_alias/value_ambient_f1_range_be2d_live.mm"
STRICT = HERE / "strict_range_imp_direct_live.mm"
REBASE = (
    ROOT / "work/mm0_conversion_2026-08-20/toolchain/hnwcut_factor_value_stage5"
    / "build_value_ambient_be2d.py"
)
MPB = ROOT / "formalization_continue/reconstruct/mmproof_builder_current.py"
OUT = HERE / "physical_helpers_before_alias0_mm0_dedup_rebuild.mm"
MARKER = "$( Linear replay source: C:/Users/glaze/Documents/Codex/2026-08-16/study-the-contents-of-this-and/work/formalization_continue/hnord_wellorder/hnwcut_ambient_strict_segment_isom_alias_checkpoint.mm $)"

F1_LABELS = [
    "hnwcutambfactorfnnoarndv",
    "hnwcutclassinjambnoarndv",
    "hnwcutambfactorf1noarndv",
    "hnwcutambfactorf1codendv",
    "hnwcutambfactorf1impclndv",
    "hnwcutambfactorf1impndv",
]
RANGE_LABELS = ["hnwcutambfactorranbrimpndv"]
STRICT_LABELS = [
    "hnwcutambclassstrictbrimpndv",
    "hnwcutambstrictsegbrimpndv",
    "hnwcutambstrictsegranimpndv",
]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


mpb = load_module("hnwcut_physical_helper_mpb", MPB)
rebaser = load_module("hnwcut_physical_helper_rebaser", REBASE)


def isolated_tail(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    match = re.match(
        r"\s*\$\(.*?\$\)\s*\$\{\s*\$\[.*?\$\]\s*\$\}\s*",
        text,
        flags=re.S,
    )
    if not match:
        raise RuntimeError(f"missing leading include-isolation wrapper: {path}")
    return text[match.end():]


def remove_floats(text: str) -> str:
    # The physical parent already has active canonical floats for every
    # metavariable in these blocks.  Keeping donor-local copies would double
    # assertion arities; the structural re-emitter maps their leaves to the
    # active canonical floats instead.
    return re.sub(
        r"(?m)^\s*[A-Za-z0-9_.-]+\s+\$f\s+(?:wff|class|setvar)\s+"
        r"[A-Za-z0-9_.-]+\s+\$\.\s*\r?\n",
        "",
        text,
    )


def replace_proof(text: str, label: str, proof: str) -> str:
    start, end, _ = rebaser.proof_span(text, label)
    return text[:start] + " " + proof + " " + text[end:]


def canonicalize_optional_floats(proof: str, target_db, theorem_label: str) -> str:
    """Retarget optional float labels to floats active in the physical root.

    The package-specific structural rebaser matches absent leaves by formal
    expression, but the last globally declared match can be a closed-scope
    helper float.  Rebuild the whole compressed table after retargeting.  A
    token-only replacement can turn an optional float into a duplicate of a
    mandatory float; some consumers collapse that duplicate and consequently
    interpret every later compressed number at the wrong offset.

    ``remap_proof`` deliberately emits a tree expansion with no saved-node
    references, so this canonicalization can losslessly decode to labels,
    deduplicate the table, and re-encode it.
    """
    tokens = proof.split()
    if not tokens or tokens[0] != "(":
        raise RuntimeError("expected compressed proof")
    close = tokens.index(")")
    mandatory = list(target_db.stmts[theorem_label].mand_hyps)
    old_table = mandatory + tokens[1:close]
    active = set(target_db.raw.frames[0]["hyps"])
    by_expr = {}
    for hyp in active:
        stmt = target_db.stmts[hyp]
        if stmt.kind == "$f":
            by_expr.setdefault(stmt.expr, hyp)

    def canonical(label: str) -> str:
        stmt = target_db.stmts.get(label)
        if stmt is not None and stmt.kind == "$f" and label not in active:
            replacement = by_expr.get(stmt.expr)
            if replacement is None:
                raise KeyError(f"no active physical float for {label}: {stmt.expr}")
            return replacement
        return label

    labels = []
    code = "".join(tokens[close + 1:])
    for item in rebaser.decode(code):
        if item == "Z" or item > len(old_table):
            raise RuntimeError("unexpected saved-node reference in remapped proof")
        labels.append(canonical(old_table[item - 1]))

    extras = []
    for label in labels:
        if label not in mandatory and label not in extras:
            extras.append(label)
    table = mandatory + extras
    encoded = "".join(rebaser.enc(table.index(label) + 1) for label in labels)
    return "( " + " ".join(extras) + " ) " + encoded


def main() -> None:
    actual = sha256(PARENT.read_bytes()).hexdigest().upper()
    if actual != PARENT_SHA:
        raise RuntimeError(f"unexpected parent SHA: {actual}")

    donors = [
        (F1, F1_LABELS),
        (RANGE, RANGE_LABELS),
        (STRICT, STRICT_LABELS),
    ]
    suffixes = [remove_floats(isolated_tail(path)) for path, _ in donors]
    parent_text = PARENT.read_text(encoding="utf-8")
    if parent_text.count(MARKER) != 1:
        raise RuntimeError("alias marker is not unique")
    all_labels = [label for _, labels in donors for label in labels]
    for label in all_labels:
        if label in parent_text:
            raise RuntimeError(f"duplicate helper label in parent: {label}")
    checkpoint = parent_text.replace(MARKER, "\n\n".join(suffixes) + "\n\n" + MARKER, 1)
    OUT.write_text(checkpoint, encoding="utf-8", newline="\n")

    target_db = mpb.load(OUT, verify=False, allow_incomplete=False)
    for donor_path, labels in donors:
        donor_db = mpb.load(donor_path, verify=False, allow_incomplete=False)
        donor_text = donor_path.read_text(encoding="utf-8")
        for label in labels:
            proof = rebaser.remap_proof(donor_text, donor_db, target_db, label)
            proof = canonicalize_optional_floats(proof, target_db, label)
            checkpoint = replace_proof(checkpoint, label, proof)
        del donor_db
        gc.collect()

    OUT.write_text(checkpoint, encoding="utf-8", newline="\n")
    mpb.load(OUT, verify=True, allow_incomplete=False)
    print(OUT)


if __name__ == "__main__":
    main()
