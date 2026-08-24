#!/usr/bin/env python3
"""Remove the one closed-scope float that poisons mm0-hs's x mapping."""

from hashlib import sha256
from pathlib import Path


HERE = Path(__file__).resolve().parent
BASE = HERE / "endpoint_after_hnwcut_alias0_scope_repaired.mm"
BASE_SHA = "3A05D138CAD97D2A75AD0E029F49FB2D71D54F6BE1DB376B0A55424F92C79AFF"
OUT = HERE / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_xfloat_scope_trial.mm"
DEDUP_BASE = HERE / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_dedup_trial.mm"
DEDUP_SHA = "AC63E2E9712407C1219813C2661F448CBAF9A61EB2A725D0B2A78DD70858CAF1"
COMBINED_OUT = HERE / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.mm"
DECL = "  hnwcutcodeeq-vx $f setvar x $.\n"


def remove_poisoning_float(source: Path, expected_sha: str) -> str:
    actual = sha256(source.read_bytes()).hexdigest().upper()
    if actual != expected_sha:
        raise RuntimeError(f"unexpected source SHA for {source.name}: {actual}")
    text = source.read_text(encoding="utf-8")
    if text.count(DECL) != 1 or text.count("hnwcutcodeeq-vx") != 2:
        raise RuntimeError("unexpected hnwcutcodeeq-vx occurrence inventory")
    text = text.replace(DECL, "", 1)
    text = text.replace("hnwcutcodeeq-vx", "vx", 1)
    if "hnwcutcodeeq-vx" in text:
        raise RuntimeError("closed-scope float reference remains")
    return text


def main() -> None:
    text = remove_poisoning_float(BASE, BASE_SHA)
    OUT.write_text(text, encoding="utf-8", newline="\n")
    print(sha256(OUT.read_bytes()).hexdigest().upper())
    print(OUT)

    combined = remove_poisoning_float(DEDUP_BASE, DEDUP_SHA)
    COMBINED_OUT.write_text(combined, encoding="utf-8", newline="\n")
    print(sha256(COMBINED_OUT.read_bytes()).hexdigest().upper())
    print(COMBINED_OUT)


if __name__ == "__main__":
    main()
