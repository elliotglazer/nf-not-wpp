#!/usr/bin/env python3
"""Independent source-only audit for immutable ``WPP_PROFILE_V2``."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
THIS = Path(__file__).resolve()
CLI = HERE / "reusable_nominal_mm_translator_v1.py"
V1 = HERE / "WPP_PROFILE_V1.json"
V2 = HERE / "WPP_PROFILE_V2.json"
BUILDER = HERE / "build_wpp_profile_v2_manifest.py"
TESTS = HERE / "test_wpp_profile_v2.py"
V1_TESTS = HERE / "test_wpp_profile_v1.py"
TRANSLATOR_TESTS = HERE / "test_reusable_nominal_mm_translator_v1.py"
ALPHA_V3_TESTS = HERE / "test_nominal_alpha_dispatch_core_v3.py"
CONTRACT = HERE / "WPP_PROFILE_V2_CONTRACT.md"
SMOKE = (
    HERE
    / "reusable_nominal_mm_translator_v1_profile_v2_smoke_001"
    / "resource.json"
)
OUT = HERE / "wpp_profile_v2_source_audit_001"
RESOURCE = OUT / "resource.json"

EXPECTED_V1_SHA256 = (
    "2DC43D9E4C07BE4B712DF4858D4EEFD16FC8D9861B093E7CDDF02EDDFEB2D2D2"
)
EXPECTED_V2_SHA256 = (
    "96B6A85D4B5B60023000C49BB40CF4F7DCD679AAF4DB6C796880A684DBF12949"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def write_exact(path: Path, content: bytes) -> None:
    require(not path.exists(), f"refusing to overwrite audit output: {path}")
    path.parent.mkdir(parents=True, exist_ok=False)
    path.write_bytes(content)


def run_tests(path: Path) -> dict[str, object]:
    run = subprocess.run(
        [sys.executable, "-B", str(path)],
        cwd=WORKSPACE,
        text=True,
        capture_output=True,
        check=False,
    )
    combined = run.stdout + run.stderr
    match = re.search(r"Ran ([0-9]+) tests?", combined)
    require(
        run.returncode == 0 and match is not None and "OK" in combined,
        f"test suite failed: {path}\n{combined}",
    )
    return {
        "path": str(path),
        "sha256": sha256(path),
        "testCount": int(match.group(1)),
        "exitCode": run.returncode,
        "status": "PASS",
    }


def open_trace_child() -> int:
    if str(HERE) not in sys.path:
        sys.path.insert(0, str(HERE))
    import reusable_nominal_mm_translator_v1 as cli

    opened: list[Path] = []

    def hook(event: str, args: tuple[Any, ...]) -> None:
        if event != "open" or not args:
            return
        value = args[0]
        if not isinstance(value, (str, bytes)):
            return
        try:
            path = Path(value.decode() if isinstance(value, bytes) else value)
            if not path.is_absolute():
                path = Path.cwd() / path
            opened.append(path.resolve())
        except (OSError, UnicodeError, ValueError):
            return

    sys.addaudithook(hook)
    profile = cli.load_wpp_profile_v2()
    backend = cli.load_backend("WPP_PROFILE_V2")
    expected = {
        Path(profile["_manifestPath"]).resolve(),
        *(path.resolve() for path in profile["_resolvedInputs"].values()),
    }
    existing_local = {
        path for path in opened
        if path.is_relative_to(WORKSPACE) and path.is_file()
    }
    prefix = Path(str(sys.pycache_prefix)).resolve()
    pyc_probes = {
        path for path in opened
        if path.suffix.lower() == ".pyc" and path.is_relative_to(prefix)
    }
    print(json.dumps({
        "profileId": profile["profileId"],
        "alphaBackend": backend.alpha_core.__name__,
        "globalRecordCount": len(backend.alpha_core.GLOBAL_RECORDS),
        "globalOrdinal72Label": backend.alpha_core.GLOBAL_RECORDS[71]["label"],
        "expectedExistingFileCount": len(expected),
        "actualExistingFileCount": len(existing_local),
        "missing": sorted(str(path) for path in expected - existing_local),
        "extra": sorted(str(path) for path in existing_local - expected),
        "pycProbeCount": len(pyc_probes),
        "allPycProbesUnderAbsentVerifiedPrefix": bool(pyc_probes)
        and all(path.is_relative_to(prefix) for path in pyc_probes)
        and not prefix.exists(),
        "existingPycReadCount": sum(path.is_file() for path in pyc_probes),
        "bytecodePrefix": str(prefix),
    }))
    return 0


def main() -> int:
    require(not OUT.exists(), f"refusing to overwrite audit output: {OUT}")
    for source in (
        CLI, BUILDER, TESTS, V1_TESTS, TRANSLATOR_TESTS,
        ALPHA_V3_TESTS, THIS,
    ):
        ast.parse(source.read_text(encoding="utf-8"), filename=str(source))
    require(sha256(V1) == EXPECTED_V1_SHA256, "WPP_PROFILE_V1 changed")
    require(sha256(V2) == EXPECTED_V2_SHA256, "WPP_PROFILE_V2 changed")

    if str(HERE) not in sys.path:
        sys.path.insert(0, str(HERE))
    import reusable_nominal_mm_translator_v1 as cli

    v1 = cli.load_wpp_profile_v1()
    v2 = cli.load_wpp_profile_v2()
    require(
        v2["inputCount"] == 97
        and v2["pythonModuleCount"] == 20
        and v2["fixedDataCount"] == 77
        and v2["inputs"][:92] == v1["inputs"],
        "V2 bounded append-only census changed",
    )
    require(
        v2["contracts"]["globalAlphaPrefix72"]
        == cli.GLOBAL_PREFIX72_CONTRACT
        and v2["contracts"]["a4972SourceMetadata"]["w1"]
        == {
            "globalOrdinal": 72,
            "surface": "wpp",
            "surfaceOrdinal": 1,
            "label": "df-iso",
            "module": "NominalAlphaRepairedWpp001001IsoStructural001",
            "sourceSha256":
                "CF76E477A68EE513FDEDFC3F7AC502A0B321BBD8EEFC9666CBE9FF1E3618CB61",
        },
        "V2 global72/W1 contract changed",
    )

    trace_run = subprocess.run(
        [sys.executable, "-B", str(THIS), "--trace-child"],
        cwd=WORKSPACE,
        text=True,
        capture_output=True,
        check=False,
    )
    require(trace_run.returncode == 0,
            f"V2 open-trace child failed: {trace_run.stderr}")
    trace = json.loads(trace_run.stdout.strip())
    require(
        trace["profileId"] == "WPP_PROFILE_V2"
        and trace["alphaBackend"] == "nominal_alpha_dispatch_core_v3"
        and trace["globalRecordCount"] == 97
        and trace["globalOrdinal72Label"] == "df-iso"
        and trace["expectedExistingFileCount"] == 98
        and trace["actualExistingFileCount"] == 98
        and trace["missing"] == []
        and trace["extra"] == []
        and trace["allPycProbesUnderAbsentVerifiedPrefix"] is True
        and trace["existingPycReadCount"] == 0,
        f"V2 static open-trace mismatch: {trace}",
    )

    suites = {
        "v2ProfileTamperAndSelection": run_tests(TESTS),
        "v1ProfileRegression": run_tests(V1_TESTS),
        "translatorRegression": run_tests(TRANSLATOR_TESTS),
        "globalAlphaV3Regression": run_tests(ALPHA_V3_TESTS),
    }
    total_tests = sum(int(report["testCount"]) for report in suites.values())
    require(total_tests == 39, "V2 audit test census changed")

    reproduce = subprocess.run(
        [sys.executable, "-B", str(BUILDER)],
        cwd=WORKSPACE,
        text=True,
        capture_output=True,
        check=False,
    )
    require(
        reproduce.returncode == 0 and sha256(V2) == EXPECTED_V2_SHA256,
        f"V2 manifest reproduction failed: {reproduce.stdout}{reproduce.stderr}",
    )

    smoke = json.loads(SMOKE.read_text(encoding="utf-8"))
    smoke_profile = smoke.get("wppProfile", {})
    audit_profile = smoke.get("sourceAudit", {}).get("wppProfile", {})
    require(
        smoke.get("status") == "PASS_SOURCE_ONLY_PREFLIGHT"
        and smoke.get("mode") == "audit-only"
        and smoke_profile == audit_profile
        and smoke_profile.get("profileId") == "WPP_PROFILE_V2"
        and smoke_profile.get("manifestSha256") == EXPECTED_V2_SHA256
        and smoke_profile.get("inputCount") == 97
        and smoke.get("sourceAudit", {}).get("checks", {}).get(
            "wppProfileVerifiedBeforeBackendImport"
        ) is True
        and smoke.get("sourceAudit", {}).get("checks", {}).get(
            "backendImportsForcedFromVerifiedSource"
        ) is True,
        "canonical audit-only smoke does not record exact V2 identity",
    )

    options = {
        option
        for action in cli.make_parser()._actions
        for option in action.option_strings
    }
    require("--wpp-profile" in options, "V2 selector is absent")
    action = next(
        action for action in cli.make_parser()._actions
        if "--wpp-profile" in action.option_strings
    )
    require(
        action.default == "WPP_PROFILE_V2"
        and tuple(action.choices) == cli.WPP_PROFILE_IDS,
        "V2 CLI selector/default changed",
    )

    resource = {
        "schema": "nf-reusable-nominal-mm-translator-wpp-profile-source-audit-v2",
        "status": "PASS_SOURCE_ONLY_WPP_PROFILE_V2_GLOBAL72_STATIC_CLOSURE",
        "leanStartedByThisAudit": False,
        "auditor": {"path": str(THIS), "sha256": sha256(THIS)},
        "implementation": {"path": str(CLI), "sha256": sha256(CLI)},
        "profile": {
            **cli.wpp_profile_provenance(v2),
            "manifestBytes": V2.stat().st_size,
            "inheritedV1InputCount": 92,
            "addedInputCount": 5,
            "globalAlphaEndOrdinal": 72,
            "globalAlphaSurfaceSequence": "B1..B71,W1",
            "w1Label": "df-iso",
        },
        "lineage": {
            "parentProfileId": "WPP_PROFILE_V1",
            "parentManifest": str(V1),
            "parentManifestSha256": EXPECTED_V1_SHA256,
            "parentInputSetSha256": v1["inputSetSha256"],
            "first92EntriesByteExact": True,
            "v1Mutated": False,
        },
        "packaging": {
            "builder": {"path": str(BUILDER), "sha256": sha256(BUILDER)},
            "contract": {"path": str(CONTRACT), "sha256": sha256(CONTRACT)},
            "manifestReproduction": "BYTE_IDENTICAL_PASS",
        },
        "tests": {**suites, "total": total_tests},
        "freshProcessOpenTrace": trace,
        "canonicalAuditOnlySmoke": {
            "resource": str(SMOKE),
            "resourceSha256": sha256(SMOKE),
            "sourceSha256": smoke["sourceAudit"]["sourceSha256"],
            "endpoint": smoke["sourceAudit"]["endpoint"],
            "selectedLabels": smoke["sourceAudit"]["selectedLabels"],
            "selectedProfileRecordedTwiceExactly": True,
            "leanStarted": False,
        },
        "compatibility": {
            "formerCliArgumentsStillAccepted": True,
            "newRequiredArguments": [],
            "optionalSelector": "--wpp-profile",
            "defaultProfile": "WPP_PROFILE_V2",
            "legacyProfileSelectable": True,
            "legacyPrefix48DelegatesToPinnedV2Dispatcher": True,
        },
        "boundedScope": {
            "sourceOnlyStaticClosureCompleteThroughGlobal72": True,
            "a4972MetadataDoesNotClaimKernelAcceptance": True,
            "runtimeAlphaFrontierStillRequiresTrustZeroExactThree": True,
            "runtimeSourceAndPredecessorRemainIndependentlyHashAuthorized": True,
            "entrypointSelfHashRecordedOutsideManifest": True,
            "leanSupportSourcesRemainKernelRunnerScope": True,
        },
        "checks": {
            "manifestPinnedBeforeParse": True,
            "all97StaticInputsPinnedBeforeBackendImport": True,
            "v1InheritedByteExactly": True,
            "actualOpenSetEqualsManifestPlusManifestFile": True,
            "noExistingPycRead": True,
            "coreV3LoadedFromVerifiedSource": True,
            "global72AndW1ContractsJoined": True,
            "focusedTamperAndRegressionTestsPass": True,
            "canonicalOutputRecordsV2Identity": True,
            "leanNotInvokedByThisAudit": True,
        },
    }
    content = (json.dumps(resource, indent=2) + "\n").encode("utf-8")
    write_exact(RESOURCE, content)
    print(json.dumps({
        "status": resource["status"],
        "resource": str(RESOURCE),
        "resourceSha256": sha256(RESOURCE),
        "profileManifestSha256": EXPECTED_V2_SHA256,
        "inputCount": v2["inputCount"],
        "tests": total_tests,
        "leanStarted": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace-child", action="store_true")
    args = parser.parse_args()
    raise SystemExit(open_trace_child() if args.trace_child else main())
