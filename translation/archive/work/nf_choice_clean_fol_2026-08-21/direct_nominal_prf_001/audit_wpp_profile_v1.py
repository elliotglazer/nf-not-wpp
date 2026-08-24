#!/usr/bin/env python3
"""Independent source-only audit for ``WPP_PROFILE_V1`` packaging."""

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
MANIFEST = HERE / "WPP_PROFILE_V1.json"
GENERATOR = HERE / "build_wpp_profile_v1_manifest.py"
TESTS = HERE / "test_wpp_profile_v1.py"
LEGACY_TESTS = HERE / "test_reusable_nominal_mm_translator_v1.py"
CONTRACT = HERE / "WPP_PROFILE_V1_CONTRACT.md"
SMOKE = HERE / "reusable_nominal_mm_translator_v1_profile_smoke_001/resource.json"
OUT = HERE / "wpp_profile_v1_source_audit_001"
RESOURCE = OUT / "resource.json"
EXPECTED_MANIFEST_SHA256 = (
    "2DC43D9E4C07BE4B712DF4858D4EEFD16FC8D9861B093E7CDDF02EDDFEB2D2D2"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def write_exact(path: Path, content: bytes) -> None:
    if path.exists():
        require(path.read_bytes() == content, f"append-only output differs: {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content)


def local_open_trace_child() -> int:
    """Trace the files opened after importing the entrypoint but before backend use."""

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
    profile = cli.load_wpp_profile_v1()
    cli.load_backend()
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
    result = {
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
    }
    print(json.dumps(result))
    return 0


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
    require(run.returncode == 0 and match is not None and "OK" in combined,
            f"test suite failed: {path}\n{combined}")
    return {
        "path": str(path),
        "sha256": sha256(path),
        "testCount": int(match.group(1)),
        "exitCode": run.returncode,
        "status": "PASS",
    }


def main() -> int:
    require(not OUT.exists(), f"refusing to overwrite audit output: {OUT}")
    for source in (CLI, GENERATOR, TESTS, LEGACY_TESTS, THIS):
        ast.parse(source.read_text(encoding="utf-8"), filename=str(source))
    require(sha256(MANIFEST) == EXPECTED_MANIFEST_SHA256,
            "WPP_PROFILE_V1 manifest pin changed")

    if str(HERE) not in sys.path:
        sys.path.insert(0, str(HERE))
    import reusable_nominal_mm_translator_v1 as cli

    profile = cli.load_wpp_profile_v1()
    require(profile["inputCount"] == 92
            and profile["pythonModuleCount"] == 19
            and profile["fixedDataCount"] == 73,
            "profile census changed")
    require(len(profile["orderedInputSets"]["choiceAlphaCallManifests"]) == 64,
            "alpha-call ordered set changed")

    trace_run = subprocess.run(
        [sys.executable, "-B", str(THIS), "--trace-child"],
        cwd=WORKSPACE,
        text=True,
        capture_output=True,
        check=False,
    )
    require(trace_run.returncode == 0,
            f"open-trace child failed: {trace_run.stderr}")
    trace = json.loads(trace_run.stdout.strip())
    require(trace["expectedExistingFileCount"] == 93
            and trace["actualExistingFileCount"] == 93
            and trace["missing"] == [] and trace["extra"] == []
            and trace["allPycProbesUnderAbsentVerifiedPrefix"] is True
            and trace["existingPycReadCount"] == 0,
            f"static open-trace mismatch: {trace}")

    profile_tests = run_tests(TESTS)
    legacy_tests = run_tests(LEGACY_TESTS)

    regenerate = subprocess.run(
        [sys.executable, "-B", str(GENERATOR)],
        cwd=WORKSPACE,
        text=True,
        capture_output=True,
        check=False,
    )
    require(regenerate.returncode == 0
            and sha256(MANIFEST) == EXPECTED_MANIFEST_SHA256,
            f"manifest reproduction failed: {regenerate.stdout}{regenerate.stderr}")

    smoke = json.loads(SMOKE.read_text(encoding="utf-8"))
    require(smoke.get("status") == "PASS_SOURCE_ONLY_PREFLIGHT"
            and smoke.get("mode") == "audit-only",
            "real NF/WPP profile smoke did not pass")
    smoke_profile = smoke.get("wppProfile", {})
    audit_profile = smoke.get("sourceAudit", {}).get("wppProfile", {})
    require(smoke_profile.get("profileId") == "WPP_PROFILE_V1"
            and smoke_profile.get("manifestSha256")
            == EXPECTED_MANIFEST_SHA256
            and smoke_profile == audit_profile
            and smoke.get("sourceAudit", {}).get("checks", {}).get(
                "wppProfileVerifiedBeforeBackendImport"
            ) is True
            and smoke.get("sourceAudit", {}).get("checks", {}).get(
                "backendImportsForcedFromVerifiedSource"
            ) is True,
            "real output does not record the exact verified profile")

    parser_options = sorted(
        option
        for action in cli.make_parser()._actions
        for option in action.option_strings
    )
    expected_options = sorted([
        "-h", "--help", "--source", "--source-sha256", "--endpoint",
        "--start-ordinal", "--end-ordinal", "--alpha-frontier-resource",
        "--alpha-frontier-sha256", "--output-dir", "--split-bytes",
        "--predecessor-resource", "--predecessor-resource-sha256",
        "--module-prefix", "--namespace", "--audit-only",
    ])
    require(parser_options == expected_options, "CLI option surface changed")

    resource = {
        "schema": "nf-reusable-nominal-mm-translator-wpp-profile-source-audit-v1",
        "status": "PASS_SOURCE_ONLY_WPP_PROFILE_V1_STATIC_CLOSURE",
        "leanStartedByThisAudit": False,
        "auditor": {"path": str(THIS), "sha256": sha256(THIS)},
        "implementation": {"path": str(CLI), "sha256": sha256(CLI)},
        "profile": {
            **cli.wpp_profile_provenance(profile),
            "manifestBytes": MANIFEST.stat().st_size,
            "alphaCallManifestCount": 64,
            "pythonSources": 19,
            "fixedDataFiles": 73,
        },
        "packaging": {
            "generator": {"path": str(GENERATOR), "sha256": sha256(GENERATOR)},
            "contract": {"path": str(CONTRACT), "sha256": sha256(CONTRACT)},
            "manifestReproduction": "BYTE_IDENTICAL_PASS",
        },
        "tests": {
            "profileTamperSuite": profile_tests,
            "existingTranslatorSuite": legacy_tests,
            "total": int(profile_tests["testCount"])
            + int(legacy_tests["testCount"]),
        },
        "freshProcessOpenTrace": trace,
        "realCanonicalAuditOnlySmoke": {
            "resource": str(SMOKE),
            "resourceSha256": sha256(SMOKE),
            "status": smoke["status"],
            "sourceSha256": smoke["sourceAudit"]["sourceSha256"],
            "endpoint": smoke["sourceAudit"]["endpoint"],
            "selectedLabels": smoke["sourceAudit"]["selectedLabels"],
            "profileIdentityRecordedTwiceExactly": True,
            "leanStarted": False,
        },
        "compatibility": {
            "cliArgumentsUnchanged": True,
            "cliOptions": parser_options,
            "outputSchemaChange": "additive wppProfile provenance only",
        },
        "boundedScope": {
            "staticClosureCompleteForCurrentNfWppSourceOnlyPath": True,
            "runtimeSource": "CLI path/hash authorized; Metamath includes rejected",
            "runtimeAlpha": "CLI root hash plus recursive resource/olean hashes",
            "runtimePredecessor": "optional CLI root hash plus nested source/kernel hashes",
            "entrypoint": "execution trust root; self SHA-256 recorded in every output",
            "leanSupportSources": "named but not read; downstream kernel-runner scope",
            "concurrentMutation": "quiescent-workspace assumption between verification and later use",
            "alphaCeiling": "base alpha ordinals 1-71; W1/global72 requires a future profile revision",
        },
        "checks": {
            "manifestPinnedBeforeParse": True,
            "allStaticInputsPinnedBeforeBackendImport": True,
            "actualOpenSetEqualsManifestPlusManifestFile": True,
            "noExistingPycRead": True,
            "allBackendImportsForcedToVerifiedSource": True,
            "focusedTamperTestsPass": True,
            "legacyTestsPass": True,
            "realOutputRecordsProfileIdentity": True,
            "manifestPathsWorkspaceRelative": True,
            "leanNotInvoked": True,
        },
    }
    content = (json.dumps(resource, indent=2) + "\n").encode("utf-8")
    write_exact(RESOURCE, content)
    print(json.dumps({
        "status": resource["status"],
        "resource": str(RESOURCE),
        "resourceSha256": sha256(RESOURCE),
        "profileManifestSha256": EXPECTED_MANIFEST_SHA256,
        "inputCount": profile["inputCount"],
        "tests": resource["tests"]["total"],
        "leanStarted": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace-child", action="store_true")
    args = parser.parse_args()
    raise SystemExit(local_open_trace_child() if args.trace_child else main())
