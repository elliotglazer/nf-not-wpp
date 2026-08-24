#!/usr/bin/env python3
"""Fail-closed source generator for the final NF |- not-WPP wrapper.

This program never invokes Lean.  It accepts only a completed 4321-theorem
translator resource and its matching trust-zero kernel resource.  It then
renders the fixed wrapper template and records every input hash.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any


SOURCE_SHA256 = "868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F"
ENDPOINT_LABEL = "wppfiniteblocknotwppndv"
ENDPOINT_AST = "(wn wwpp)"
ENDPOINT_ORDINAL = 4321
ENDPOINT_DEF = "g_wppfiniteblocknotwppndv"
ENDPOINT_FQ = "NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv"
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
FINAL_MODULE = "NominalWPPFinalEndpointV1"
FINAL_THEOREM = (
    "NFChoice.DirectNominalPrf.Nominal.WPPFinalEndpointV1."
    "hailperinNF_proves_not_WPP"
)

# The template hash is filled by the package source audit and checked by the
# runner.  Keeping it as an explicit command-line pin avoids a self-hash cycle.
TEMPLATE_NAME = "NOMINAL_WPP_FINAL_ENDPOINT_V1.lean.in"

STATIC_INPUTS = {
    "canonicalMetamath": (
        "work/mm0_conversion_2026-08-20/source_repair/hnwcut_resisomr_assist/"
        "endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.mm",
        SOURCE_SHA256,
    ),
    "closedEndpointBridge": (
        "work/nf_choice_clean_fol_2026-08-21/direct_nominal_prf_001/"
        "NominalClosedEndpointBridgeV1.lean",
        "6585D25D9B2333D7EFE3EB264E5E75131B9247EB48D9DE2E55994993C0C7C2D5",
    ),
    "nominalProofBoundary": (
        "work/nf_choice_clean_fol_2026-08-21/direct_nominal_prf_001/"
        "NominalWffPrf.lean",
        "987B1BDE1815040729F21006FF8D52F63AA7975B3ED3516B2F3A51CDA44F9979",
    ),
    "exactLiteralTheory": (
        "work/nf_choice_clean_fol_2026-08-21/foundation/exact_literal_trial/"
        "NFChoiceExactLiteral.lean",
        "1E98C0E0B9BA90B9501A7160DFE27D836B86E78698F00C1D9DB43160FC83574A",
    ),
    "foundationAxiomNames": (
        "work/nf_choice_clean_fol_2026-08-21/foundation/"
        "NFChoiceFoundation/Basic.lean",
        "24605D1DABC31EF37F7C58A7D573756DD0F53DC962F3A112883277287D1F075D",
    ),
    "wppEndpoint": (
        "work/nf_wpp_clean_fol_2026-08-21/endpoint/WPPCompactEndpoint.lean",
        "AC8EF4214E303BB1B7D8C293DB18181303464335B3A4659773C3A35521733D75",
    ),
    "wppSyntax": (
        "work/nf_wpp_clean_fol_2026-08-21/definition_leaves/audit_surface_002/"
        "WPPCompactSourceSyntax.lean",
        "EED1484C89AF7BA7186B2D022C4D6BE5CB1156EA07B9423CD22D6D714A219CE1",
    ),
    "wppFreeVariables": (
        "work/nf_wpp_clean_fol_2026-08-21/definition_leaves/audit_surface_002/"
        "WPPCompactSyntaxFVExplicit.lean",
        "E09FA6176086DFFA998C20DEF8A782252B9D50A0873181A32E1E2C887A6E65F4",
    ),
    "boundedLoweringBridge": (
        "work/nf_choice_clean_fol_2026-08-21/"
        "direct_certificate_005_nf_handlers_001/BoundedNominalLoweringBridgeDev004.lean",
        "1A9858C34648F6F90F45A4C1F94F210BDC10D4F18B80F7BA924DB597F8D020D6",
    ),
    "closureCensus": (
        "work/nf_choice_clean_fol_2026-08-21/direct_nominal_prf_001/"
        "remaining_wpp_closure_census_001/resource.json",
        "F02231E398CF86EFA54AB947936B0B5D668F9D2F3C7C7DD35C46FFB76FF7749A",
    ),
    "translatorProfileAudit": (
        "work/nf_choice_clean_fol_2026-08-21/direct_nominal_prf_001/"
        "wpp_profile_v2_source_audit_001/resource.json",
        "38C63085D71EAA3454D25D24DD9E50B5449B984CF58EDB13A53A310ABFC3A346",
    ),
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest().upper()


def demand(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_json(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    demand(isinstance(data, dict), f"JSON root is not an object: {path}")
    return data


def resolve_recorded(value: str, anchor: Path) -> Path:
    candidate = Path(value)
    if not candidate.is_absolute():
        candidate = anchor.parent / candidate
    return candidate.resolve(strict=True)


def assert_hash(path: Path, expected: str, context: str) -> str:
    demand(re.fullmatch(r"[0-9A-Fa-f]{64}", expected) is not None,
           f"bad SHA-256 pin for {context}")
    actual = sha256(path)
    demand(actual == expected.upper(),
           f"SHA-256 mismatch for {context}: {actual} != {expected.upper()}")
    return actual


def workspace_root() -> Path:
    root = Path(__file__).resolve().parents[3]
    demand((root / "work").is_dir(), "could not locate workspace root")
    return root


def audit_static_inputs(root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for name, (relative, expected) in STATIC_INPUTS.items():
        path = (root / relative).resolve(strict=True)
        actual = assert_hash(path, expected, name)
        rows.append({
            "name": name,
            "path": str(path),
            "bytes": path.stat().st_size,
            "sha256": actual,
        })

    mm_text = (root / STATIC_INPUTS["canonicalMetamath"][0]).read_text(
        encoding="utf-8"
    )
    demand(re.search(
        r"(?m)^wppfiniteblocknotwppndv\s+\$p\s+\|-\s+-\.\s+WPP\s+\$=",
        mm_text,
    ) is not None, "canonical source endpoint is not `|- -. WPP`")

    nominal_text = (root / STATIC_INPUTS["nominalProofBoundary"][0]).read_text(
        encoding="utf-8"
    )
    demand(re.search(
        r"def\s+NPrf\s+\(p\s*:\s*Wff\)\s*:\s*Type\s*:=\s*"
        r"∀\s+rho\s*:\s*Var\s*→\s*Nat,\s*"
        r"Fol\.prf\s+LiteralHailperinNF\.fst\s*\(lowerWff\s+rho\s+p\)",
        nominal_text,
    ) is not None, "Nominal.NPrf is not the exact syntactic Flypitch boundary")

    exact_text = (root / STATIC_INPUTS["exactLiteralTheory"][0]).read_text(
        encoding="utf-8"
    )
    demand("abbrev LiteralHailperinNF : Fol.SentTheory LNF :=\n  Set.range literalAxiomFormula"
           in exact_text, "LiteralHailperinNF boundary changed")
    for constructor in (
        "axExt", "axNin", "axXp", "axCnv", "ax1c", "axSset", "axSi",
        "axIns2", "axIns3", "axTypeLower", "axSn",
    ):
        demand(f"| .{constructor} =>" in exact_text,
               f"missing literal Hailperin axiom: {constructor}")

    endpoint_text = (root / STATIC_INPUTS["wppEndpoint"][0]).read_text(
        encoding="utf-8"
    )
    demand("def SourceWPPCompact : Wff :=\n  syn_wwpp" in endpoint_text,
           "SourceWPPCompact is not definitionally syn_wwpp")
    demand("LiteralHailperinNF ⊢ₛ' Fol.bd_not SourceWPPFOL" in endpoint_text,
           "public WPP endpoint type changed")

    bridge_text = (root / STATIC_INPUTS["closedEndpointBridge"][0]).read_text(
        encoding="utf-8"
    )
    demand("(generatedEndpoint : Nominal.NPrf (Wff.neg syn_wwpp))" in bridge_text,
           "closed bridge no longer accepts the exact generated endpoint")
    demand("LiteralHailperinNF ⊢ₛ' Fol.bd_not SourceWPPFOL" in bridge_text,
           "closed bridge public result changed")
    demand(re.search(r"(?m)^\s*(axiom|opaque)\b|\bsorry\b", bridge_text) is None,
           "forbidden declaration or placeholder in closed endpoint bridge")
    return rows


def validate_source_resource(path: Path, expected_sha: str) -> tuple[dict[str, Any], str]:
    actual_sha = assert_hash(path, expected_sha, "final source resource")
    data = read_json(path)
    demand(data.get("sourceSha256") == SOURCE_SHA256,
           "final source resource does not pin the canonical repaired source")
    demand(data.get("endpoint") == ENDPOINT_LABEL, "wrong source endpoint label")
    demand(data.get("endpointAst") == ENDPOINT_AST, "wrong endpoint AST")
    demand(data.get("closureProofTheoremCount") == ENDPOINT_ORDINAL,
           "wrong closure theorem count")
    demand(data.get("endTheoremOrdinal") == ENDPOINT_ORDINAL,
           "final source resource does not end at theorem 4321")
    parts = data.get("parts")
    demand(isinstance(parts, list) and parts, "final source resource has no parts")
    demand(parts[-1].get("lastLabel") == ENDPOINT_LABEL,
           "last emitted theorem is not the endpoint")
    umbrella = data.get("umbrellaModule")
    demand(isinstance(umbrella, dict), "missing final umbrella module")
    demand(umbrella.get("endpoint") == ENDPOINT_DEF, "wrong umbrella endpoint")
    module = umbrella.get("module")
    demand(isinstance(module, str) and re.fullmatch(
        r"[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*", module
    ) is not None, "invalid final replay module name")
    source_path = resolve_recorded(str(data.get("source")), path)
    assert_hash(source_path, SOURCE_SHA256, "resource-recorded Metamath source")
    return data, actual_sha


def validate_kernel_resource(
    path: Path,
    expected_sha: str,
    source_path: Path,
    source_sha: str,
    replay_module: str,
) -> tuple[dict[str, Any], str, Path, str, list[str]]:
    actual_sha = assert_hash(path, expected_sha, "final kernel resource")
    data = read_json(path)
    demand(data.get("status") ==
           "PASS_TRUST_ZERO_ALL_PARTS_AND_UMBRELLA_EXACT_THREE",
           "final replay kernel resource is not a completed exact-three run")
    demand(data.get("allowedAxioms") == ALLOWED_AXIOMS,
           "final replay allowed-axiom list is not exactly the standard three")
    source_record = data.get("sourceResource")
    demand(isinstance(source_record, dict), "kernel resource has no sourceResource")
    recorded_source = resolve_recorded(str(source_record.get("path")), path)
    demand(recorded_source == source_path.resolve(),
           "kernel resource points to a different source resource")
    demand(str(source_record.get("sha256", "")).upper() == source_sha,
           "kernel/source resource hash linkage mismatch")

    command = data.get("umbrellaCommand")
    demand(isinstance(command, dict), "kernel resource has no umbrella command")
    demand(command.get("module") == replay_module, "kernel umbrella module mismatch")
    demand(command.get("trust") == 0 and command.get("exitCode") == 0,
           "kernel umbrella was not accepted at trust zero")
    demand(command.get("killed") is False and command.get("emptyStderr") is True,
           "kernel umbrella process contract failed")
    demand(command.get("exactAllowedThree") is True,
           "kernel umbrella did not print exactly the allowed three")
    demand(command.get("printedTheorem") == ENDPOINT_FQ,
           "kernel umbrella printed a theorem other than the exact endpoint")
    olean = resolve_recorded(str(command.get("output")), path)
    olean_sha = assert_hash(olean, str(command.get("outputSha256")),
                            "final replay umbrella olean")

    roots = data.get("leanPath")
    demand(isinstance(roots, list) and roots, "kernel resource has no LEAN_PATH")
    resolved_roots: list[str] = []
    for value in roots:
        demand(isinstance(value, str), "non-string LEAN_PATH entry")
        root = resolve_recorded(value, path)
        demand(root.is_dir(), f"LEAN_PATH entry is not a directory: {root}")
        resolved_roots.append(str(root))
    demand(str(olean.parent) in resolved_roots,
           "final replay olean root is absent from its kernel LEAN_PATH")
    return data, actual_sha, olean, olean_sha, resolved_roots


def render(replay_module: str, template_text: str) -> str:
    demand(template_text.count("@@FINAL_REPLAY_MODULE@@") == 1,
           "template placeholder count is not one")
    rendered = template_text.replace("@@FINAL_REPLAY_MODULE@@", replay_module)
    demand(re.search(r"(?m)^\s*(axiom|opaque)\b|\bsorry\b", rendered) is None,
           "forbidden declaration or placeholder in rendered wrapper")
    demand(f"import {replay_module}" in rendered, "rendered replay import mismatch")
    demand(ENDPOINT_FQ in rendered, "rendered wrapper does not use exact endpoint")
    demand("LiteralHailperinNF ⊢ₛ' Fol.bd_not SourceWPPFOL" in rendered,
           "rendered wrapper does not state the exact public result")
    return rendered


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--final-source-resource", required=True, type=Path)
    parser.add_argument("--final-source-resource-sha256", required=True)
    parser.add_argument("--final-kernel-resource", required=True, type=Path)
    parser.add_argument("--final-kernel-resource-sha256", required=True)
    parser.add_argument("--template", type=Path,
                        default=Path(__file__).with_name(TEMPLATE_NAME))
    parser.add_argument("--template-sha256", required=True)
    parser.add_argument("--output-dir", required=True, type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = workspace_root()
    static_rows = audit_static_inputs(root)

    source_path = args.final_source_resource.resolve(strict=True)
    source, source_sha = validate_source_resource(
        source_path, args.final_source_resource_sha256
    )
    replay_module = str(source["umbrellaModule"]["module"])
    kernel_path = args.final_kernel_resource.resolve(strict=True)
    _, kernel_sha, olean, olean_sha, lean_path = validate_kernel_resource(
        kernel_path,
        args.final_kernel_resource_sha256,
        source_path,
        source_sha,
        replay_module,
    )

    template = args.template.resolve(strict=True)
    template_sha = assert_hash(template, args.template_sha256, "wrapper template")
    rendered = render(replay_module, template.read_text(encoding="utf-8"))

    output = args.output_dir.resolve()
    demand(not output.exists(), f"refusing to overwrite output directory: {output}")
    output.mkdir(parents=True, exist_ok=False)
    wrapper = output / f"{FINAL_MODULE}.lean"
    wrapper.write_text(rendered, encoding="utf-8", newline="\n")
    wrapper_sha = sha256(wrapper)

    provenance = {
        "schema": "nf-nominal-wpp-final-endpoint-source-v1",
        "status": "PASS_SOURCE_ONLY_READY_FOR_TRUST_ZERO",
        "leanStartedByThisProducer": False,
        "canonicalEndpoint": {
            "sourceSha256": SOURCE_SHA256,
            "label": ENDPOINT_LABEL,
            "ast": ENDPOINT_AST,
            "closureTheoremCount": ENDPOINT_ORDINAL,
            "generatedTheorem": ENDPOINT_FQ,
        },
        "publicResult": {
            "theorem": FINAL_THEOREM,
            "type": "LiteralHailperinNF ⊢ₛ' Fol.bd_not SourceWPPFOL",
            "axiomCountInObjectTheoryBasis": 11,
            "requiredLeanAxiomsAfterKernelCheck": ALLOWED_AXIOMS,
        },
        "sourceResource": {"path": str(source_path), "sha256": source_sha},
        "kernelResource": {"path": str(kernel_path), "sha256": kernel_sha},
        "replayUmbrella": {
            "module": replay_module,
            "olean": str(olean),
            "oleanSha256": olean_sha,
        },
        "template": {"path": str(template), "sha256": template_sha},
        "wrapper": {
            "module": FINAL_MODULE,
            "path": str(wrapper),
            "bytes": wrapper.stat().st_size,
            "sha256": wrapper_sha,
            "printedTheorem": FINAL_THEOREM,
        },
        "staticInputs": static_rows,
        "leanPathFromKernelResource": lean_path,
    }
    provenance_path = output / "source_resource.json"
    provenance_path.write_text(
        json.dumps(provenance, indent=2, sort_keys=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps({
        "status": provenance["status"],
        "module": FINAL_MODULE,
        "wrapperSha256": wrapper_sha,
        "sourceResource": str(provenance_path),
        "sourceResourceSha256": sha256(provenance_path),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
