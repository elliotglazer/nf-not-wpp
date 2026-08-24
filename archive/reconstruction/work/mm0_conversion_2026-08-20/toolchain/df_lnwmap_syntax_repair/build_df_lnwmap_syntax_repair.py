#!/usr/bin/env python3
"""Repair the malformed function-value subexpressions in ``df-lnwmap``.

This is deliberately an assertion-only source repair.  It starts from the
DE0C scope-repair checkpoint, replaces one exact token sequence, verifies the
result with both local Python proof checkers, reruns the strict-scope audit,
and records a statement/proof delta audit before freezing the checkpoint.

No Metamath executable is invoked by this script.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[3]
PYTHON = Path(sys.executable)
INPUT = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/toolchain/cfb_codecover_scope_repair/"
    "endpoint_after_cfb_codecover_frozen_checkpoint.mm"
)
OUTPUT = HERE / "endpoint_after_df_lnwmap.mm"
FROZEN = HERE / "endpoint_after_df_lnwmap_frozen_checkpoint.mm"
PRIMARY = (
    WORKSPACE
    / "work/formalization_continue/root_integration/local_mm_verify_compressed.py"
)
SECONDARY = (
    WORKSPACE
    / "work/formalization_continue/release_final_2026-08-17/"
    "formalization_continue/reconstruct/mmverify_simple.py"
)
STRICT = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/strict_scope/"
    "local_mm_verify_compressed_strict_scope.py"
)
DELTA_TOOL = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/source_repair/"
    "audit_scope_repair_token_delta.py"
)
PRIMARY_REPORT = OUTPUT.with_suffix(".primary.json")
STRICT_REPORT = OUTPUT.with_suffix(".strict_scope.json")
DELTA_REPORT = OUTPUT.with_suffix(".delta.json")
AUDIT = OUTPUT.with_suffix(".audit.json")
PRELOAD_NORMALIZER = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/input_prep/"
    "normalize_compressed_preloads_for_mm0.py"
)
NORMALIZED = HERE / "endpoint_after_df_lnwmap_preloads_normalized.mm"
NORMALIZED_PRIMARY_REPORT = NORMALIZED.with_suffix(".primary.json")
MM0_HS = WORKSPACE / "work/mm0_conversion_2026-08-20/toolchain/bin/mm0-hs.exe"
MM0_OUT = HERE / "endpoint_after_df_lnwmap.mm0"
MMU_OUT = HERE / "endpoint_after_df_lnwmap.mmu"

OLD = """df-lnwmap $a |- LNWMap A =
    ( u e. ~P1 LNPWC A |->
      LNWCode ( 1st ` U. u , 2nd ` U. u ) ) $."""

NEW = """df-lnwmap $a |- LNWMap A =
    ( u e. ~P1 LNPWC A |->
      LNWCode ( ( 1st ` U. u ) , ( 2nd ` U. u ) ) ) $."""


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def run(args: list[str], expected: int = 0) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        args,
        cwd=WORKSPACE,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != expected:
        raise RuntimeError(
            f"return {result.returncode}, expected {expected}: {args!r}\n"
            + result.stdout[-5000:]
            + result.stderr[-5000:]
        )
    return result


def main() -> int:
    source = INPUT.read_text(encoding="utf-8")
    if source.count(OLD) != 1:
        raise RuntimeError(f"expected one exact df-lnwmap source, found {source.count(OLD)}")
    repaired = source.replace(OLD, NEW, 1)
    if repaired.count(NEW) != 1:
        raise RuntimeError("repaired df-lnwmap assertion is not unique")
    OUTPUT.write_text(repaired, encoding="utf-8", newline="\n")

    run([str(PYTHON), str(PRIMARY), str(OUTPUT), str(PRIMARY_REPORT)])
    secondary = run([str(PYTHON), str(SECONDARY), str(OUTPUT)])
    run([str(PYTHON), str(STRICT), str(OUTPUT), str(STRICT_REPORT)], expected=1)
    run([str(PYTHON), str(DELTA_TOOL), str(INPUT), str(OUTPUT), str(DELTA_REPORT)])

    primary = json.loads(PRIMARY_REPORT.read_text(encoding="utf-8"))
    strict = json.loads(STRICT_REPORT.read_text(encoding="utf-8"))
    delta = json.loads(DELTA_REPORT.read_text(encoding="utf-8"))
    if not primary.get("ok") or primary.get("trusted") != 0:
        raise RuntimeError(f"primary verification failed: {primary}")
    if strict.get("rejected_proof_count") != 2:
        raise RuntimeError(f"unexpected strict inventory: {strict.get('rejected_proofs')}")
    if strict.get("rejected_proofs") != [
        "wppstopfixedhitcontrgrowfixdndv",
        "hnwcutambstrictsegresisomralias0ndv",
    ]:
        raise RuntimeError(f"unexpected strict theorem list: {strict.get('rejected_proofs')}")
    expected_delta = {
        "changed_assertion_formulas": ["df-lnwmap"],
        "changed_proofs": [],
        "changed_kinds": [],
        "added_labels": [],
        "removed_labels": [],
        "structure_identical": True,
    }
    for key, value in expected_delta.items():
        if delta.get(key) != value:
            raise RuntimeError(f"unexpected delta for {key}: {delta.get(key)!r}")

    FROZEN.write_bytes(OUTPUT.read_bytes())

    # ``from-mm`` rejects redundant mandatory $e labels in compressed-proof
    # preload tables.  Normalize only those redundant entries before the
    # stock-importer probe, and independently verify the normalized result.
    preload = run(
        [str(PYTHON), str(PRELOAD_NORMALIZER), str(FROZEN), str(NORMALIZED)]
    )
    run(
        [
            str(PYTHON),
            str(PRIMARY),
            str(NORMALIZED),
            str(NORMALIZED_PRIMARY_REPORT),
        ]
    )
    normalized_secondary = run([str(PYTHON), str(SECONDARY), str(NORMALIZED)])
    importer = run(
        [
            str(MM0_HS),
            "from-mm",
            str(NORMALIZED),
            "-f",
            "wppfiniteblocknotwppndv",
            "-o",
            str(MM0_OUT),
            str(MMU_OUT),
        ],
        expected=1,
    )
    importer_diagnostic = (importer.stdout + importer.stderr).strip()
    if importer_diagnostic != (
        "at wppstopfixedhitcontrgrowfixdndv: $e found in paren list"
    ):
        raise RuntimeError(f"unexpected stock importer diagnostic: {importer_diagnostic!r}")
    normalized_primary = json.loads(
        NORMALIZED_PRIMARY_REPORT.read_text(encoding="utf-8")
    )
    preload_report = json.loads(
        NORMALIZED.with_suffix(".preload_normalization.json").read_text(
            encoding="utf-8"
        )
    )
    if (
        not normalized_primary.get("ok")
        or normalized_primary.get("verified") != 4329
        or normalized_primary.get("trusted") != 0
    ):
        raise RuntimeError(f"normalized primary verification failed: {normalized_primary}")
    if preload_report.get("changed_proof_count") != 7:
        raise RuntimeError(f"unexpected preload normalization: {preload_report}")

    audit = {
        "repair": "df-lnwmap function-value parenthesization",
        "repair_kind": "assertion-formula syntax repair",
        "source": str(INPUT),
        "source_sha256": sha256(INPUT),
        "output": str(OUTPUT),
        "output_sha256": sha256(OUTPUT),
        "frozen_checkpoint": str(FROZEN),
        "frozen_checkpoint_sha256": sha256(FROZEN),
        "primary_verified": primary.get("verified"),
        "primary_trusted": primary.get("trusted"),
        "secondary_stdout": secondary.stdout.strip(),
        "strict_rejected_proof_count": strict.get("rejected_proof_count"),
        "strict_rejected_proofs": strict.get("rejected_proofs"),
        "changed_assertion_formulas": delta.get("changed_assertion_formulas"),
        "changed_proofs": delta.get("changed_proofs"),
        "changed_kinds": delta.get("changed_kinds"),
        "added_labels": delta.get("added_labels"),
        "removed_labels": delta.get("removed_labels"),
        "structure_identical": delta.get("structure_identical"),
        "downstream_proof_regeneration_required": False,
        "preload_normalized_copy": str(NORMALIZED),
        "preload_normalized_copy_sha256": sha256(NORMALIZED),
        "preload_normalized_changed_proof_count": preload_report.get(
            "changed_proof_count"
        ),
        "preload_normalized_primary_verified": normalized_primary.get("verified"),
        "preload_normalized_primary_trusted": normalized_primary.get("trusted"),
        "preload_normalized_secondary_stdout": normalized_secondary.stdout.strip(),
        "stock_mm0_hs": str(MM0_HS),
        "stock_mm0_hs_sha256": sha256(MM0_HS),
        "stock_from_mm_exit_code": importer.returncode,
        "stock_from_mm_diagnostic": importer_diagnostic,
        "stock_from_mm_passed_df_lnwmap": True,
        "stock_from_mm_next_blocker_is_pending_scope_repair": True,
        "metamath_executable_invoked": False,
    }
    AUDIT.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(audit, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
