"""Install the scope-clean PWPull deduction proof into the endpoint slice."""

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
DEFAULT_INPUT = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/source_repair/"
    "endpoint_after_fdminvalp_pointcover_frozen_checkpoint.mm"
)
INPUT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else DEFAULT_INPUT
OUTPUT = (
    Path(sys.argv[2]).resolve()
    if len(sys.argv) > 2
    else HERE / "endpoint_after_pointcover_pwpull.mm"
)
FROZEN = HERE / "endpoint_after_pointcover_pwpull_frozen_checkpoint.mm"
PROOF = HERE / "pwpullwesetimp_scope_clean_proof.txt"
GENERATOR = HERE / "generate_pwpull_scope_clean_proof.py"
LAX = (
    WORKSPACE
    / "work/formalization_continue/root_integration/local_mm_verify_compressed.py"
)
STRICT = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/strict_scope/"
    "local_mm_verify_compressed_strict_scope.py"
)
SECONDARY = (
    WORKSPACE
    / "work/formalization_continue/release_final_2026-08-17/"
    "formalization_continue/reconstruct/mmverify_simple.py"
)
DELTA_TOOL = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/source_repair/"
    "audit_scope_repair_token_delta.py"
)
LAX_REPORT = OUTPUT.with_suffix(".lax.json")
STRICT_REPORT = OUTPUT.with_suffix(".strict_scope.json")
DELTA_REPORT = OUTPUT.with_suffix(".delta.json")
AUDIT = OUTPUT.with_suffix(".audit.json")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def install_proof(text: str, proof: str) -> str:
    pattern = re.compile(
        r"(pwpullwesetimpndv\s+\$p\s+.*?\$=)\s*.*?\s*\$\.",
        re.S,
    )
    text, count = pattern.subn(
        lambda match: match.group(1) + " " + proof.strip() + " $.",
        text,
        count=1,
    )
    if count != 1:
        raise RuntimeError(f"pwpullwesetimpndv replacement count: {count}")
    return text


def run_checked(args: list[str], expected: int = 0) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        args,
        cwd=WORKSPACE,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != expected:
        raise RuntimeError(
            f"command returned {result.returncode}, expected {expected}: {args!r}\n"
            + result.stdout[-4000:]
            + result.stderr[-4000:]
        )
    return result


def main() -> int:
    if not PROOF.exists():
        run_checked([str(PYTHON), str(GENERATOR)])
    text = INPUT.read_text(encoding="utf-8")
    proof = PROOF.read_text(encoding="utf-8")
    OUTPUT.write_text(install_proof(text, proof), encoding="utf-8", newline="\n")

    run_checked([str(PYTHON), str(LAX), str(OUTPUT), str(LAX_REPORT)])
    secondary = run_checked([str(PYTHON), str(SECONDARY), str(OUTPUT)])
    # The point-cover parent has five remaining bad proofs.  This repair
    # removes PWPull, leaving the four independently assigned violations.
    run_checked(
        [str(PYTHON), str(STRICT), str(OUTPUT), str(STRICT_REPORT)],
        expected=1,
    )
    lax = json.loads(LAX_REPORT.read_text(encoding="utf-8"))
    strict = json.loads(STRICT_REPORT.read_text(encoding="utf-8"))
    if not lax.get("ok") or lax.get("trusted") != 0:
        raise RuntimeError(f"unexpected lax verifier result: {lax}")
    run_checked(
        [str(PYTHON), str(DELTA_TOOL), str(INPUT), str(OUTPUT), str(DELTA_REPORT)]
    )
    delta = json.loads(DELTA_REPORT.read_text(encoding="utf-8"))
    if strict.get("rejected_proof_count") != 4:
        raise RuntimeError(
            "strict rejected-proof count is not the expected 4: "
            + repr(strict.get("rejected_proofs"))
        )
    if any(
        item.get("theorem") == "pwpullwesetimpndv"
        for item in strict.get("inactive_hypothesis_references", [])
    ):
        raise RuntimeError("pwpullwesetimpndv is still scope-invalid")
    if delta.get("changed_proofs") != ["pwpullwesetimpndv"]:
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
        "generated_proof": str(PROOF),
        "generated_proof_sha256": sha256(PROOF),
        "lax_verified": lax.get("verified"),
        "lax_trusted": lax.get("trusted"),
        "strict_rejected_proof_count": strict.get("rejected_proof_count"),
        "strict_rejected_proofs": strict.get("rejected_proofs"),
        "secondary_stdout": secondary.stdout.strip(),
        "changed_proofs": delta.get("changed_proofs"),
        "changed_assertion_formulas": delta.get("changed_assertion_formulas"),
        "structure_identical": delta.get("structure_identical"),
        "frozen_checkpoint": str(FROZEN),
        "frozen_checkpoint_sha256": sha256(FROZEN),
        "repair": "identity-safe dependency cache; regenerate pwpullwesetimpndv",
        "metamath_executable_invoked": False,
    }
    AUDIT.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(audit, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
