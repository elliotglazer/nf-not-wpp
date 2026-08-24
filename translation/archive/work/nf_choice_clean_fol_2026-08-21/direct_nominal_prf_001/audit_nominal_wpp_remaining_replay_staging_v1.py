#!/usr/bin/env python3
"""Independent source-only audit of the remaining NF/WPP replay staging."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import Sequence

import build_nominal_wpp_remaining_replay_plan_v1 as planner


HERE = Path(__file__).resolve().parent
AUDIT = Path(__file__).resolve()
PLAN = HERE / "nominal_wpp_remaining_replay_staging_001" / "plan.json"
PLAN_SHA256 = "F60772608E3074F98822234D8A541E2C952764EB8D5566B08B159EBB864AB628"
RUNNER = HERE / "run_nominal_wpp_remaining_replay_translation_v1.py"
TEST = HERE / "test_nominal_wpp_remaining_replay_staging_v1.py"
BUILDER = HERE / "build_nominal_wpp_remaining_replay_plan_v1.py"
README = HERE / "nominal_wpp_remaining_replay_staging_001" / "README.md"
ALPHA49 = HERE / "a49op1r1" / "resource.json"
ALPHA49_SHA256 = "7F2367A3D5ED3D82836028A6258440CF0CD3E0FD31388E6CBC775590ACAE43D2"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=False) + "\n").encode("utf-8")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def audit_runner_ast() -> dict[str, object]:
    source = RUNNER.read_text(encoding="utf-8")
    tree = ast.parse(source, filename=str(RUNNER))
    subprocess_calls: list[tuple[str, int]] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        function = node.func
        if (
            isinstance(function, ast.Attribute)
            and isinstance(function.value, ast.Name)
            and function.value.id == "subprocess"
        ):
            subprocess_calls.append((function.attr, node.lineno))
    require(len(subprocess_calls) == 1 and subprocess_calls[0][0] == "run",
            f"unexpected runner subprocess surface: {subprocess_calls}")
    require("Path(command[1]).resolve() == planner.TRANSLATOR.resolve()" in source,
            "runner lacks its pinned-translator execution guard")
    require("--trust" not in source,
            "source-only runner unexpectedly contains a Lean trust argument")
    require("lean.exe" not in source.lower(),
            "source-only runner unexpectedly names the Lean executable")
    return {
        "pythonSubprocessCallCount": 1,
        "pythonSubprocessCalls": [
            {"function": name, "line": line} for name, line in subprocess_calls
        ],
        "pinnedTranslatorExecutionGuardPresent": True,
        "leanExecutableNamed": False,
        "leanTrustArgumentPresent": False,
    }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    output = args.output.resolve()
    require(output.parent.is_dir(), f"output parent does not exist: {output.parent}")
    require(not output.exists(), f"refusing to overwrite audit: {output}")
    require(sha256(PLAN) == PLAN_SHA256, "frozen plan hash changed")
    rebuilt = planner.json_bytes(planner.build_plan())
    require(PLAN.read_bytes() == rebuilt, "fresh checked-source plan differs")
    plan = json.loads(rebuilt.decode("utf-8"))
    require(
        plan["remainingInterval"]["theoremCount"] == 1455
        and plan["partitionPolicy"]["chunkCount"] == 7
        and plan["chunks"][0]["startTheoremOrdinal"] == 2867
        and plan["chunks"][-1]["endTheoremOrdinal"] == 4321
        and plan["chunks"][-1]["lastLabel"] == planner.ENDPOINT,
        "remaining interval plan changed",
    )
    runner_ast = audit_runner_ast()

    tests = subprocess.run(
        [sys.executable, str(TEST)],
        cwd=HERE,
        text=True,
        encoding="utf-8",
        capture_output=True,
        check=False,
    )
    require(tests.returncode == 0,
            f"source-only tests failed:\n{tests.stdout}\n{tests.stderr}")
    require("Ran 9 tests" in tests.stderr and "OK" in tests.stderr,
            "unit-test output did not report 9/9 passing")

    invalid_session = output.parent.parent / "invalid_alpha49_should_not_exist.json"
    invalid_preflight = output.parent.parent / (
        "nominal_wpp_remaining_replay_alpha97_preflight_001"
    )
    require(not invalid_session.exists() and not invalid_preflight.exists(),
            "negative-probe output exists before the audit")
    invalid = subprocess.run(
        [
            sys.executable,
            str(RUNNER),
            "--alpha-frontier-resource", str(ALPHA49),
            "--alpha-frontier-sha256", ALPHA49_SHA256,
            "--output-parent", str(output.parent.parent),
            "--session-resource", str(invalid_session),
        ],
        cwd=HERE,
        text=True,
        encoding="utf-8",
        capture_output=True,
        check=False,
    )
    require(invalid.returncode != 0, "alpha49 negative probe unexpectedly succeeded")
    require("does not end at exact global ordinal 97" in invalid.stderr,
            "alpha49 negative probe failed for an unexpected reason")
    require(not invalid_session.exists() and not invalid_preflight.exists(),
            "alpha49 negative probe created output")

    artifacts = []
    for path in (AUDIT, BUILDER, PLAN, RUNNER, TEST, README):
        artifacts.append(
            {
                "path": path.relative_to(HERE).as_posix(),
                "bytes": path.stat().st_size,
                "sha256": sha256(path),
            }
        )
    resource = {
        "schema": "nf-wpp-remaining-replay-staging-independent-audit-v1",
        "status": "PASS_INDEPENDENT_SOURCE_ONLY_PLAN_AND_GATE_AUDIT_NO_LEAN",
        "leanStartedByAudit": False,
        "auditProducer": AUDIT.relative_to(HERE).as_posix(),
        "auditProducerSha256": sha256(AUDIT),
        "plan": str(PLAN),
        "planSha256": PLAN_SHA256,
        "sourceSha256": planner.SOURCE_SHA256,
        "endpoint": planner.ENDPOINT,
        "endpointAst": planner.ENDPOINT_AST,
        "closureProofTheoremCount": planner.CLOSURE_THEOREM_COUNT,
        "remainingStartTheoremOrdinal": planner.REMAINING_START,
        "remainingEndTheoremOrdinal": planner.REMAINING_END,
        "remainingTheoremCount": 1455,
        "chunkCount": 7,
        "firstRemainingLabel": "isoeq1",
        "finalLabel": planner.ENDPOINT,
        "releaseId": "NF_WPP_TRANSLATOR_TOOLCHAIN_002",
        "translatorSha256": planner.TRANSLATOR_SHA256,
        "profileSha256": planner.PROFILE_SHA256,
        "acceptedPredecessorResourceSha256":
            planner.PREDECESSOR_RESOURCE_SHA256,
        "alpha97AcceptanceState": "PENDING_EXTERNAL_KERNEL_RESOURCE",
        "alpha49NegativeProbeExitCode": invalid.returncode,
        "alpha49NegativeProbeCreatedOutput": False,
        "unitTests": {
            "path": TEST.relative_to(HERE).as_posix(),
            "count": 9,
            "exitCode": tests.returncode,
            "result": "OK",
        },
        "runnerStaticAudit": runner_ast,
        "artifacts": artifacts,
        "kernelVerificationSeparate": True,
    }
    content = json_bytes(resource)
    output.write_bytes(content)
    require(output.read_bytes() == content, "published audit resource changed")
    print(f"PASS wrote audit {output} sha256={sha256_bytes(content)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
