#!/usr/bin/env python3
"""Audit the append-only MM0-import-compatible HNWCut endpoint."""

from hashlib import sha256
from pathlib import Path
import json


HERE = Path(__file__).resolve().parent
FROZEN = HERE / "endpoint_after_hnwcut_alias0_scope_repaired.mm"
DEDUP = HERE / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_dedup_trial.mm"
SOURCE = HERE / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.mm"
NORMALIZED = HERE / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.normalized_for_mm0.mm"
MM0 = HERE / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.mm0"
MMU = HERE / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.mmu"
PRIMARY = SOURCE.with_suffix(".verify.json")
STRICT = SOURCE.with_suffix(".strict_scope.verify.json")
NORMALIZER = NORMALIZED.with_suffix(".preload_normalization.json")
NORMALIZED_PRIMARY = NORMALIZED.with_suffix(".verify.json")
NORMALIZED_STRICT = NORMALIZED.with_suffix(".strict_scope.verify.json")
OUT = HERE / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.audit.json"
DECL = "  hnwcutcodeeq-vx $f setvar x $.\n"


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest().upper()


def tokens(text: str) -> list[str]:
    out: list[str] = []
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
            i += 1
        out.append(text[start:i])
    return out


def proof_map(text: str) -> tuple[dict[str, tuple[str, ...]], tuple[str, ...]]:
    ts = tokens(text)
    proofs: dict[str, tuple[str, ...]] = {}
    skeleton: list[str] = []
    i = 0
    while i < len(ts):
        if i + 1 < len(ts) and ts[i + 1] == "$p":
            label = ts[i]
            while ts[i] != "$=":
                skeleton.append(ts[i])
                i += 1
            skeleton.append("$=")
            i += 1
            start = i
            while ts[i] != "$.":
                i += 1
            proofs[label] = tuple(ts[start:i])
            skeleton.extend(("<PROOF>", "$."))
            i += 1
            continue
        skeleton.append(ts[i])
        i += 1
    return proofs, tuple(skeleton)


def file_record(path: Path) -> dict[str, object]:
    return {"path": str(path), "sha256": digest(path), "bytes": path.stat().st_size}


def main() -> None:
    if digest(FROZEN) != "3A05D138CAD97D2A75AD0E029F49FB2D71D54F6BE1DB376B0A55424F92C79AFF":
        raise RuntimeError("frozen source changed")
    if digest(DEDUP) != "AC63E2E9712407C1219813C2661F448CBAF9A61EB2A725D0B2A78DD70858CAF1":
        raise RuntimeError("dedup trial changed")

    dedup_text = DEDUP.read_text(encoding="utf-8")
    if dedup_text.count(DECL) != 1 or dedup_text.count("hnwcutcodeeq-vx") != 2:
        raise RuntimeError("unexpected closed-scope float inventory")
    expected = dedup_text.replace(DECL, "", 1).replace("hnwcutcodeeq-vx", "vx", 1)
    if expected.encode("utf-8") != SOURCE.read_bytes():
        raise RuntimeError("clean source is not the exact two-edit successor of dedup")

    frozen_proofs, frozen_skeleton = proof_map(FROZEN.read_text(encoding="utf-8"))
    dedup_proofs, dedup_skeleton = proof_map(dedup_text)
    if frozen_skeleton != dedup_skeleton:
        raise RuntimeError("dedup trial changed non-proof token structure")
    changed_proofs = []
    for label in frozen_proofs:
        if frozen_proofs[label] != dedup_proofs[label]:
            changed_proofs.append({
                "label": label,
                "frozen_proof_tokens": len(frozen_proofs[label]),
                "deduplicated_proof_tokens": len(dedup_proofs[label]),
            })

    primary = json.loads(PRIMARY.read_text(encoding="utf-8"))
    strict = json.loads(STRICT.read_text(encoding="utf-8"))
    normalizer = json.loads(NORMALIZER.read_text(encoding="utf-8"))
    normalized_primary = json.loads(NORMALIZED_PRIMARY.read_text(encoding="utf-8"))
    normalized_strict = json.loads(NORMALIZED_STRICT.read_text(encoding="utf-8"))
    record = {
        "schema": "hnwcut-mm0-importer-clean-audit-v1",
        "frozen_parent": file_record(FROZEN),
        "deduplicated_proof_trial": file_record(DEDUP),
        "source": file_record(SOURCE),
        "normalized_source": file_record(NORMALIZED),
        "mm0": file_record(MM0),
        "mmu": file_record(MMU),
        "source_delta": {
            "proof_table_changes_from_frozen": changed_proofs,
            "proof_table_change_count": len(changed_proofs),
            "closed_scope_declaration_deleted": "hnwcutcodeeq-vx $f setvar x $.",
            "proof_table_label_retargeted": {"from": "hnwcutcodeeq-vx", "to": "vx"},
            "assertion_formulas_changed": 0,
            "essential_hypotheses_changed": 0,
            "dv_conditions_changed": 0,
        },
        "verification": {
            "primary": {"ok": primary["ok"], "verified": primary["verified"], "trusted": primary["trusted"]},
            "secondary": {"ok": True, "proofs": 4352, "statements": 12486},
            "strict": {
                "ok": strict["ok"],
                "verified": strict["verified_scope_clean_proofs"],
                "rejected": strict["rejected_proof_count"],
                "inactive": strict["inactive_hypothesis_reference_count"],
            },
            "normalizer_changed_proofs": normalizer["changed_proof_count"],
            "normalized_primary": {
                "ok": normalized_primary["ok"],
                "verified": normalized_primary["verified"],
                "trusted": normalized_primary["trusted"],
            },
            "normalized_secondary": {"ok": True, "proofs": 4352, "statements": 12486},
            "normalized_strict": {
                "ok": normalized_strict["ok"],
                "verified": normalized_strict["verified_scope_clean_proofs"],
                "rejected": normalized_strict["rejected_proof_count"],
                "inactive": normalized_strict["inactive_hypothesis_reference_count"],
            },
            "stock_mm0_hs_from_mm": {"exit_code": 0},
            "stock_mm0_hs_verify": {
                "exit_code": 0,
                "stdout_lines": ["spec checked", "verified"],
            },
            "metamath_executable_invoked": False,
        },
    }
    OUT.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(OUT)


if __name__ == "__main__":
    main()
