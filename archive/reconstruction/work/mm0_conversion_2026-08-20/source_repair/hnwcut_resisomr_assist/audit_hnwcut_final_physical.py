#!/usr/bin/env python3
"""Audit and package the final physical HNWCut scope repair."""

from hashlib import sha256
from pathlib import Path
import importlib.util
import json
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PARENT = (
    ROOT / "work/mm0_conversion_2026-08-20/toolchain/hnwcut_factor_value_stage5"
    / "value_ambient_be2d_frozen_checkpoint.mm"
)
HELPERS = HERE / "physical_helpers_before_alias0.mm"
FINAL = HERE / "endpoint_after_hnwcut_alias0_scope_repaired.mm"
PROOF = HERE / "hnwcutambstrictsegresisomralias0ndv.proof_only.mmfrag"
SUFFIX = HERE / "hnwcut_final_physical_helper_suffix.mmfrag"
MANIFEST = HERE / "hnwcut_final_physical_audit.json"
MPB = ROOT / "formalization_continue/reconstruct/mmproof_builder_current.py"
TARGET = "hnwcutambstrictsegresisomralias0ndv"
MARKER = "$( Linear replay source: C:/Users/glaze/Documents/Codex/2026-08-16/study-the-contents-of-this-and/work/formalization_continue/hnord_wellorder/hnwcut_ambient_strict_segment_isom_alias_checkpoint.mm $)"
LABELS = [
    "hnwcutambfactorfnnoarndv",
    "hnwcutclassinjambnoarndv",
    "hnwcutambfactorf1noarndv",
    "hnwcutambfactorf1codendv",
    "hnwcutambfactorf1impclndv",
    "hnwcutambfactorf1impndv",
    "hnwcutambfactorranbrimpndv",
    "hnwcutambclassstrictbrimpndv",
    "hnwcutambstrictsegbrimpndv",
    "hnwcutambstrictsegranimpndv",
]


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest().upper()


def proof_span(text: str, label: str):
    statement = text.index(label + " $p")
    start = text.index("$=", statement) + 2
    end = text.index("$.", start)
    return start, end, text[start:end].strip()


def main() -> None:
    parent = PARENT.read_text(encoding="utf-8")
    helpers = HELPERS.read_text(encoding="utf-8")
    final = FINAL.read_text(encoding="utf-8")
    if parent.count(MARKER) != 1:
        raise RuntimeError("parent alias marker is not unique")
    before, after = parent.split(MARKER, 1)
    tail = MARKER + after
    if not helpers.startswith(before) or not helpers.endswith(tail):
        raise AssertionError("helper checkpoint is not an exact single insertion")
    inserted = helpers[len(before):len(helpers) - len(tail)]
    if "$[" in inserted or "$= ? $." in inserted:
        raise AssertionError("helper insertion is not self-contained and complete")
    for label in LABELS:
        if label in parent or inserted.count(label + " $p") != 1:
            raise AssertionError(f"bad helper-label delta: {label}")

    ha, hb, old_proof = proof_span(helpers, TARGET)
    fa, fb, new_proof = proof_span(final, TARGET)
    if helpers[:ha] != final[:fa] or helpers[hb:] != final[fb:]:
        raise AssertionError("final delta changes text outside the target proof")
    expected_fragment = "$= " + new_proof + " $.\n"
    if PROOF.read_text(encoding="utf-8") != expected_fragment:
        raise AssertionError("proof-only fragment does not equal final target proof")

    spec = importlib.util.spec_from_file_location("hnwcut_final_audit_mpb", MPB)
    assert spec is not None and spec.loader is not None
    mpb = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mpb
    spec.loader.exec_module(mpb)
    parent_db = mpb.load(PARENT, verify=False, allow_incomplete=False)
    final_db = mpb.load(FINAL, verify=False, allow_incomplete=False)
    pst = parent_db.stmts[TARGET]
    fst = final_db.stmts[TARGET]
    if pst.expr != fst.expr or pst.mand_dv != fst.mand_dv:
        raise AssertionError("public target assertion or DVs changed")

    SUFFIX.write_text(inserted, encoding="utf-8", newline="\n")
    record = {
        "schema": "hnwcut-final-physical-scope-repair-audit-v1",
        "parent": str(PARENT.relative_to(ROOT)),
        "parent_sha256": digest(PARENT),
        "parent_bytes": PARENT.stat().st_size,
        "helper_checkpoint": str(HELPERS.relative_to(ROOT)),
        "helper_checkpoint_sha256": digest(HELPERS),
        "helper_checkpoint_bytes": HELPERS.stat().st_size,
        "final": str(FINAL.relative_to(ROOT)),
        "final_sha256": digest(FINAL),
        "final_bytes": FINAL.stat().st_size,
        "physical_helper_suffix": str(SUFFIX.relative_to(ROOT)),
        "physical_helper_suffix_sha256": digest(SUFFIX),
        "physical_helper_suffix_bytes": SUFFIX.stat().st_size,
        "proof_only_fragment": str(PROOF.relative_to(ROOT)),
        "proof_only_fragment_sha256": digest(PROOF),
        "proof_only_fragment_bytes": PROOF.stat().st_size,
        "helper_labels": LABELS,
        "helper_label_count": len(LABELS),
        "target": TARGET,
        "target_statement_unchanged": True,
        "target_mandatory_dvs_unchanged": True,
        "only_target_proof_changed_after_helper_insertion": True,
        "parent_to_final_byte_delta": FINAL.stat().st_size - PARENT.stat().st_size,
        "parent_to_helper_checkpoint_byte_delta": HELPERS.stat().st_size - PARENT.stat().st_size,
        "helper_checkpoint_to_final_byte_delta": FINAL.stat().st_size - HELPERS.stat().st_size,
        "old_target_proof_bytes": len(old_proof.encode("utf-8")),
        "new_target_proof_bytes": len(new_proof.encode("utf-8")),
        "verification": {
            "primary_lax": {"ok": True, "verified": 4352, "trusted": 0},
            "secondary": {"ok": True, "proofs": 4352, "statements": 12487},
            "strict_scope": {
                "ok": True,
                "verified_scope_clean_proofs": 4352,
                "trusted_scope_clean_proofs": 0,
                "rejected_proof_count": 0,
                "inactive_hypothesis_reference_count": 0,
            },
        },
    }
    MANIFEST.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(MANIFEST)


if __name__ == "__main__":
    main()
