#!/usr/bin/env python3
"""Independent source-only audit of the final endpoint package."""

from __future__ import annotations

import argparse
import ast
import hashlib
import importlib.util
import json
import re
from pathlib import Path
from typing import Any


INDEPENDENT_STATIC_PINS = {
    "canonicalMetamath": "868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F",
    "closedEndpointBridge": "6585D25D9B2333D7EFE3EB264E5E75131B9247EB48D9DE2E55994993C0C7C2D5",
    "nominalProofBoundary": "987B1BDE1815040729F21006FF8D52F63AA7975B3ED3516B2F3A51CDA44F9979",
    "exactLiteralTheory": "1E98C0E0B9BA90B9501A7160DFE27D836B86E78698F00C1D9DB43160FC83574A",
    "foundationAxiomNames": "24605D1DABC31EF37F7C58A7D573756DD0F53DC962F3A112883277287D1F075D",
    "wppEndpoint": "AC8EF4214E303BB1B7D8C293DB18181303464335B3A4659773C3A35521733D75",
    "wppSyntax": "EED1484C89AF7BA7186B2D022C4D6BE5CB1156EA07B9423CD22D6D714A219CE1",
    "wppFreeVariables": "E09FA6176086DFFA998C20DEF8A782252B9D50A0873181A32E1E2C887A6E65F4",
    "boundedLoweringBridge": "1A9858C34648F6F90F45A4C1F94F210BDC10D4F18B80F7BA924DB597F8D020D6",
    "closureCensus": "F02231E398CF86EFA54AB947936B0B5D668F9D2F3C7C7DD35C46FFB76FF7749A",
    "translatorProfileAudit": "38C63085D71EAA3454D25D24DD9E50B5449B984CF58EDB13A53A310ABFC3A346",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def demand(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    return parser.parse_args()


def file_record(path: Path) -> dict[str, Any]:
    return {
        "path": str(path.resolve()),
        "bytes": path.stat().st_size,
        "sha256": sha256(path),
    }


def main() -> int:
    args = parse_args()
    base = Path(__file__).resolve().parent
    root = base.parents[2]
    generator = base / "generate_nominal_wpp_final_endpoint_v1.py"
    template = base / "NOMINAL_WPP_FINAL_ENDPOINT_V1.lean.in"
    runner = base / "run_nominal_wpp_final_endpoint_trust0_v1.ps1"
    contract = base / "NOMINAL_WPP_FINAL_ENDPOINT_V1_CONTRACT.md"
    bridge = base / "NominalClosedEndpointBridgeV1.lean"
    for path in (generator, template, runner, contract, bridge):
        demand(path.is_file(), f"missing package file: {path}")

    ast.parse(generator.read_text(encoding="utf-8"), filename=str(generator))
    ast.parse(Path(__file__).read_text(encoding="utf-8"), filename=str(Path(__file__)))

    spec = importlib.util.spec_from_file_location("final_endpoint_generator", generator)
    demand(spec is not None and spec.loader is not None, "cannot load generator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    demand(module.SOURCE_SHA256 ==
           "868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F",
           "canonical source hash constant mismatch")
    demand(module.ENDPOINT_LABEL == "wppfiniteblocknotwppndv", "endpoint mismatch")
    demand(module.ENDPOINT_AST == "(wn wwpp)", "endpoint AST mismatch")
    demand(module.ENDPOINT_ORDINAL == 4321, "endpoint ordinal mismatch")
    demand(module.ALLOWED_AXIOMS == ["propext", "Classical.choice", "Quot.sound"],
           "allowed Lean axioms mismatch")

    demand(set(module.STATIC_INPUTS) == set(INDEPENDENT_STATIC_PINS),
           "generator static-input set differs from independent audit set")
    for name, expected in INDEPENDENT_STATIC_PINS.items():
        demand(module.STATIC_INPUTS[name][1] == expected,
               f"generator pin differs from independent pin: {name}")
    static_rows = module.audit_static_inputs(module.workspace_root())
    demand(len(static_rows) == len(module.STATIC_INPUTS), "static input audit incomplete")
    for row in static_rows:
        demand(row["sha256"] == INDEPENDENT_STATIC_PINS[row["name"]],
               f"observed static hash differs from independent pin: {row['name']}")

    template_text = template.read_text(encoding="utf-8")
    rendered = module.render("SyntheticFinalReplayModule001", template_text)
    demand("import SyntheticFinalReplayModule001" in rendered,
           "template smoke render failed")
    demand(module.ENDPOINT_FQ in rendered, "exact generated endpoint absent")
    demand(module.FINAL_THEOREM in rendered.replace(
        "#print axioms hailperinNF_proves_not_WPP",
        "#print axioms " + module.FINAL_THEOREM,
    ), "final theorem name contract mismatch")
    demand(re.search(r"(?m)^\s*(axiom|opaque)\b|\bsorry\b", rendered) is None,
           "forbidden declaration or placeholder in template")

    runner_text = runner.read_text(encoding="utf-8-sig")
    for token in (
        "--trust=0", "--threads=1", "Assert-ExactPrints",
        "PASS_TRUST_ZERO_EXACT_ELEVEN_NF_PROVES_NOT_WPP_EXACT_THREE",
        "sequentialSingleLeanProcess=$true",
        "LiteralHailperinNF ⊢ₛ' Fol.bd_not SourceWPPFOL",
    ):
        demand(token in runner_text, f"runner contract token absent: {token}")
    demand("Start-Process" not in runner_text, "runner uses shell-quoting-sensitive Start-Process")
    demand(runner_text.count("Invoke-LeanModule") == 3,
           "runner should define one Lean invoker and call it exactly twice")

    support = [
        (
            root / "work/nf_wpp_clean_fol_2026-08-21/endpoint/audit_002/"
                   "WPPCompactEndpoint.olean",
            "WPPCompactEndpoint",
            "D3EDECDE3821A4234C3C363D047F6FB7363506C8DAAF3EEC615AE5800A2AE65B",
        ),
        (
            root / "work/nf_choice_clean_fol_2026-08-21/"
                   "direct_certificate_005_nf_handlers_001/bounded_nominal_attempt_004/"
                   "BoundedNominalLoweringBridgeDev004.olean",
            "BoundedNominalLoweringBridgeDev004",
            "67048EF06FCD22890BB962870D6192DED25263944B7AF6C5C686EB7C586AAC2C",
        ),
        (
            root / "work/nf_choice_clean_fol_2026-08-21/"
                   "direct_certificate_005_nf_handlers_001/partial_total_attempt_002/"
                   "PartialTotalizationBridgeDev002.olean",
            "PartialTotalizationBridgeDev002",
            "4349AB573ED46D6EB7AF5768A314F2B7A4C3D6FCF0420BF672FB7FDEC8369D1D",
        ),
        (
            root / "work/nf_choice_clean_fol_2026-08-21/compiler/"
                   "endpoint_link_001/audit_totalized_001/EndpointLoweringTotality.olean",
            "EndpointLoweringTotality",
            "369947D9549998664778837460F89031CB1F21BCFB5430F85A5528885671C3B2",
        ),
        (
            root / "work/nf_wpp_clean_fol_2026-08-21/definition_leaves/"
                   "audit_surface_002/WPPCompactSyntaxFVExplicit.olean",
            "WPPCompactSyntaxFVExplicit",
            "A06A5CCF7C0F45359C0D26D10ABD0C58887AD7FC59434136835FEAF6BF34F689",
        ),
        (
            root / "work/nf_choice_clean_fol_2026-08-21/replay_support/"
                   "ReplaySupport/Basic.olean",
            "ReplaySupport.Basic",
            "BD290039CF2EA0B34134BA744F62695EBCC92DE1C6CF36F6EE1F8834076C53C0",
        ),
    ]
    support_rows = []
    for path, name, expected in support:
        demand(path.is_file(), f"missing support olean: {path}")
        demand(sha256(path) == expected, f"support olean hash mismatch: {name}")
        row = file_record(path)
        row["module"] = name
        support_rows.append(row)

    output = args.output.resolve()
    demand(not output.exists(), f"refusing to overwrite audit resource: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    resource = {
        "schema": "nf-nominal-wpp-final-endpoint-package-source-audit-v1",
        "status": "PASS_SOURCE_ONLY_FINAL_ENDPOINT_PACKAGE_V1",
        "leanStartedByThisAudit": False,
        "files": {
            "generator": file_record(generator),
            "template": file_record(template),
            "runner": file_record(runner),
            "contract": file_record(contract),
            "bridge": file_record(bridge),
            "auditor": file_record(Path(__file__)),
        },
        "canonicalEndpoint": {
            "sourceSha256": module.SOURCE_SHA256,
            "label": module.ENDPOINT_LABEL,
            "ast": module.ENDPOINT_AST,
            "closureTheoremCount": module.ENDPOINT_ORDINAL,
            "generatedTheorem": module.ENDPOINT_FQ,
        },
        "publicResult": {
            "theorem": module.FINAL_THEOREM,
            "type": "LiteralHailperinNF ⊢ₛ' Fol.bd_not SourceWPPFOL",
            "objectTheoryAxiomCount": 11,
            "kernelAxiomExpectation": module.ALLOWED_AXIOMS,
        },
        "staticInputs": static_rows,
        "supportOleans": support_rows,
        "sourceOnlyChecks": {
            "pythonSyntax": "PASS",
            "staticHashes": "PASS",
            "exactEndpointAndTypeAssertions": "PASS",
            "templateSmokeRender": "PASS",
            "forbiddenLeanDeclarations": "PASS",
            "runnerTrustZeroExactThreeContract": "PASS",
            "leanProcessesStarted": 0,
        },
        "pending": (
            "Supply the completed theorem-4321 translator resource and matching "
            "trust-zero kernel resource to the pinned runner."
        ),
    }
    output.write_text(json.dumps(resource, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({
        "status": resource["status"],
        "resource": str(output),
        "resourceSha256": sha256(output),
        "leanStarted": False,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
