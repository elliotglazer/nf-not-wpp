"""Regenerate and audit the two-stage ``cfbhnqinjcodecoverddndv`` proof."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[3]
PYTHON = Path(sys.executable)
INPUT = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/toolchain/hnqinc_scope_repair/"
    "endpoint_after_hnqinc_frozen_checkpoint.mm"
)
PRE = (
    WORKSPACE
    / "work/formalization_continue/cumulative_finite_block/"
    "common_ambient_hartogs_graph/pointwise_transport/pointwise_transport_pre.mm"
)
GENERATOR = HERE / "generate_scope_clean_deduction.py"
D_PROOF = HERE / "cfbhnqinjcodecoverdndv_scope_clean_proof.txt"
DD_PRE = HERE / "cfb_codecover_dd_scope_clean_pre.mm"
DD_PROOF = HERE / "cfbhnqinjcodecoverddndv_scope_clean_proof.txt"
OUTPUT = HERE / "endpoint_after_cfb_codecover.mm"
FROZEN = HERE / "endpoint_after_cfb_codecover_frozen_checkpoint.mm"
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
            + result.stdout[-4000:]
            + result.stderr[-4000:]
        )
    return result


def install(text: str, label: str, proof: str) -> str:
    pattern = re.compile(
        rf"({re.escape(label)}\s+\$p\s+.*?\$=)\s*.*?\s*\$\.", re.S
    )
    text, count = pattern.subn(
        lambda match: match.group(1) + " " + proof.strip() + " $.",
        text,
        count=1,
    )
    if count != 1:
        raise RuntimeError(f"{label} replacement count: {count}")
    return text


def absolutize_includes(text: str, source_dir: Path) -> str:
    """Preserve include resolution after moving the temporary prefile."""

    pattern = re.compile(r"\$\[\s+(\S+)\s+\$\]")

    def replace(match: re.Match[str]) -> str:
        include = (source_dir / match.group(1)).resolve()
        return "$[ " + include.as_posix() + " $]"

    return pattern.sub(replace, text)


def main() -> int:
    # Run each transform in a fresh process so its retained-node cache is
    # released before the next stage starts.
    if not D_PROOF.exists():
        run(
            [
                str(PYTHON),
                str(GENERATOR),
                str(PRE),
                "cfbhnqinjcodecoverndv",
                "cfbhnqinjcodecoverdndv",
                "cfbhnqinjcodecoverndv.4",
                str(D_PROOF),
            ]
        )
    d_pre_text = install(
        PRE.read_text(encoding="utf-8"),
        "cfbhnqinjcodecoverdndv",
        D_PROOF.read_text(encoding="utf-8"),
    )
    d_pre_text = absolutize_includes(d_pre_text, PRE.parent)
    DD_PRE.write_text(d_pre_text, encoding="utf-8", newline="\n")
    if not DD_PROOF.exists():
        run(
            [
                str(PYTHON),
                str(GENERATOR),
                str(DD_PRE),
                "cfbhnqinjcodecoverdndv",
                "cfbhnqinjcodecoverddndv",
                "cfbhnqinjcodecoverdndv.3",
                str(DD_PROOF),
            ]
        )
    dd_proof = DD_PROOF.read_text(encoding="utf-8")
    for forbidden in (
        "cfbhnqinjcodecoverdndv.3",
        "cfbhnqinjcodecoverndv.4",
    ):
        if forbidden in dd_proof:
            raise RuntimeError(f"final proof still names inactive {forbidden}")

    OUTPUT.write_text(
        install(
            INPUT.read_text(encoding="utf-8"),
            "cfbhnqinjcodecoverddndv",
            dd_proof,
        ),
        encoding="utf-8",
        newline="\n",
    )
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
    if any(
        item.get("theorem") == "cfbhnqinjcodecoverddndv"
        for item in strict.get("inactive_hypothesis_references", [])
    ):
        raise RuntimeError("cfbhnqinjcodecoverddndv is still scope-invalid")
    if delta.get("changed_proofs") != ["cfbhnqinjcodecoverddndv"]:
        raise RuntimeError(f"unexpected proof delta: {delta}")
    if (
        delta.get("changed_assertion_formulas")
        or delta.get("changed_kinds")
        or delta.get("added_labels")
        or delta.get("removed_labels")
        or not delta.get("structure_identical")
    ):
        raise RuntimeError(f"unexpected formula/structure delta: {delta}")

    FROZEN.write_bytes(OUTPUT.read_bytes())
    audit = {
        "source": str(INPUT),
        "source_sha256": sha256(INPUT),
        "output": str(OUTPUT),
        "output_sha256": sha256(OUTPUT),
        "frozen_checkpoint": str(FROZEN),
        "frozen_checkpoint_sha256": sha256(FROZEN),
        "first_stage_proof": str(D_PROOF),
        "first_stage_proof_sha256": sha256(D_PROOF),
        "final_proof": str(DD_PROOF),
        "final_proof_sha256": sha256(DD_PROOF),
        "primary_verified": primary.get("verified"),
        "primary_trusted": primary.get("trusted"),
        "secondary_stdout": secondary.stdout.strip(),
        "strict_rejected_proof_count": strict.get("rejected_proof_count"),
        "strict_rejected_proofs": strict.get("rejected_proofs"),
        "changed_proofs": delta.get("changed_proofs"),
        "changed_assertion_formulas": delta.get("changed_assertion_formulas"),
        "structure_identical": delta.get("structure_identical"),
        "metamath_executable_invoked": False,
    }
    AUDIT.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(audit, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
