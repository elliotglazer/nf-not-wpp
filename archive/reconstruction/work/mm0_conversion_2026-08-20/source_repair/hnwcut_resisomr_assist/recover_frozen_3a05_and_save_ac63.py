#!/usr/bin/env python3
"""Restore the frozen 3A05 artifact and retain the AC63 importer trial.

This is a one-shot recovery utility.  The frozen helper suffix and proof-only
fragment were packaged before the importer trial, so together with the pinned
BE2D parent they reconstruct the exact frozen files byte for byte.
"""

from hashlib import sha256
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PARENT = (
    ROOT / "work/mm0_conversion_2026-08-20/toolchain/hnwcut_factor_value_stage5"
    / "value_ambient_be2d_frozen_checkpoint.mm"
)
FROZEN_HELPERS = HERE / "physical_helpers_before_alias0.mm"
FROZEN_FINAL = HERE / "endpoint_after_hnwcut_alias0_scope_repaired.mm"
TRIAL_HELPERS = HERE / "physical_helpers_before_alias0_mm0_dedup_trial.mm"
TRIAL_FINAL = HERE / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_dedup_trial.mm"
SUFFIX = HERE / "hnwcut_final_physical_helper_suffix.mmfrag"
PROOF = HERE / "hnwcutambstrictsegresisomralias0ndv.proof_only.mmfrag"
TARGET = "hnwcutambstrictsegresisomralias0ndv"
MARKER = "$( Linear replay source: C:/Users/glaze/Documents/Codex/2026-08-16/study-the-contents-of-this-and/work/formalization_continue/hnord_wellorder/hnwcut_ambient_strict_segment_isom_alias_checkpoint.mm $)"
EXPECTED_HELPERS = "E88B80A205C1797FB2CCA37FA6B5353B34F4A818AA7476F06246ED2DA0D31905"
EXPECTED_FINAL = "3A05D138CAD97D2A75AD0E029F49FB2D71D54F6BE1DB376B0A55424F92C79AFF"


def digest(data: bytes) -> str:
    return sha256(data).hexdigest().upper()


def main() -> None:
    # Preserve the current canonical-dedup experiment under append-only names.
    TRIAL_HELPERS.write_bytes(FROZEN_HELPERS.read_bytes())
    TRIAL_FINAL.write_bytes(FROZEN_FINAL.read_bytes())

    parent = PARENT.read_text(encoding="utf-8")
    if parent.count(MARKER) != 1:
        raise RuntimeError("parent marker is not unique")
    helpers = parent.replace(MARKER, SUFFIX.read_text(encoding="utf-8") + MARKER, 1)
    helper_bytes = helpers.encode("utf-8")
    if digest(helper_bytes) != EXPECTED_HELPERS:
        raise RuntimeError(f"helper reconstruction mismatch: {digest(helper_bytes)}")

    fragment = PROOF.read_text(encoding="utf-8")
    if not fragment.startswith("$= ") or not fragment.endswith(" $.\n"):
        raise RuntimeError("unexpected proof-only fragment framing")
    proof = fragment[3:-4]
    pattern = re.compile(
        r"(" + re.escape(TARGET) + r"\s+\$p\s+.*?\$=)\s*.*?\s*\$\.", re.S
    )
    final, count = pattern.subn(
        lambda match: match.group(1) + " " + proof + " $.", helpers, count=1
    )
    if count != 1:
        raise RuntimeError(f"target replacement count: {count}")
    final_bytes = final.encode("utf-8")
    if digest(final_bytes) != EXPECTED_FINAL:
        raise RuntimeError(f"final reconstruction mismatch: {digest(final_bytes)}")

    FROZEN_HELPERS.write_bytes(helper_bytes)
    FROZEN_FINAL.write_bytes(final_bytes)
    print(TRIAL_FINAL)
    print(FROZEN_FINAL)


if __name__ == "__main__":
    main()
