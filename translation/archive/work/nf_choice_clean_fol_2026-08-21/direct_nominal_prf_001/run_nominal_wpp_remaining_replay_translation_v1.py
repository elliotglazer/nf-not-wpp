#!/usr/bin/env python3
"""Fail-closed source translation for NF/WPP theorem ordinals 2867--4321.

The caller must supply the eventual accepted alpha97 kernel resource and its
SHA-256.  This runner never invokes Lean.  It first asks the release002
translator to audit the full remaining interval, then emits seven append-only
logical chunks and verifies every generated resource against the frozen plan.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any, Mapping, Sequence

import build_nominal_wpp_remaining_replay_plan_v1 as planner


HERE = Path(__file__).resolve().parent
PLAN = HERE / "nominal_wpp_remaining_replay_staging_001" / "plan.json"
PLAN_SHA256 = "F60772608E3074F98822234D8A541E2C952764EB8D5566B08B159EBB864AB628"
PREFLIGHT_DIRECTORY = "nominal_wpp_remaining_replay_alpha97_preflight_001"
PREFLIGHT_MODULE = "NominalWPPReplayRemaining28674321Alpha97Preflight001"
SHA256_RE = re.compile(r"^[0-9A-F]{64}$")
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=False) + "\n").encode("utf-8")


def canonical_json_sha256(value: object) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return sha256_bytes(payload)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def normalized_sha256(value: str, description: str) -> str:
    result = value.upper()
    require(SHA256_RE.fullmatch(result) is not None,
            f"invalid {description} SHA-256: {value!r}")
    return result


def require_hash(path: Path, expected: str, description: str) -> None:
    require(path.is_file(), f"missing {description}: {path}")
    actual = sha256(path)
    require(actual == expected, f"{description} hash mismatch: {actual} != {expected}")


def load_plan() -> dict[str, Any]:
    require_hash(PLAN, PLAN_SHA256, "frozen remaining-replay plan")
    frozen = PLAN.read_bytes()
    rebuilt = planner.json_bytes(planner.build_plan())
    require(frozen == rebuilt, "frozen plan differs from a fresh checked-source rebuild")
    data = json.loads(frozen.decode("utf-8"))
    require(isinstance(data, dict), "remaining-replay plan is not a JSON object")
    require(
        data.get("status")
        == "PASS_SOURCE_ONLY_DETERMINISTIC_PLAN_ALPHA97_KERNEL_PENDING",
        "remaining-replay plan has an unexpected status",
    )
    return data


def validate_alpha97_data(data: Any) -> dict[str, Any]:
    require(isinstance(data, dict), "alpha97 resource is not a JSON object")
    require(
        str(data.get("status", "")).startswith("PASS_KERNEL_FIRST_USE_PREFIX_")
        and isinstance(data.get("firstUsePrefix"), Mapping),
        "alpha97 resource is not an accepted first-use kernel frontier",
    )
    trust = data.get("trust")
    require(type(trust) is int and trust == 0,
            "alpha97 resource was not accepted at trust level zero")
    prefix = data["firstUsePrefix"]
    end = prefix.get("endOrdinal")
    require(type(end) is int and end == 97,
            "alpha frontier does not end at exact global ordinal 97")
    require(data.get("allowedAxioms") == ALLOWED_AXIOMS,
            "alpha97 resource does not publish the exact allowed-three list")
    audit = data.get("audit")
    require(isinstance(audit, Mapping), "alpha97 resource has no kernel audit")
    require(
        (audit.get("exactAllowedThreeAll") is True
         or audit.get("exactAllowedThree") is True)
        and audit.get("exitCode") == 0
        and audit.get("exitCode") is not False
        and audit.get("killed") is False
        and audit.get("emptyStderr") is True
        and audit.get("forbiddenAxiomMatches") == [],
        "alpha97 resource lacks the exact-three successful kernel audit",
    )
    return data


def load_alpha97_resource(path: Path, expected_sha256: str) -> dict[str, Any]:
    path = path.resolve()
    expected = normalized_sha256(expected_sha256, "alpha97 resource")
    require_hash(path, expected, "accepted alpha97 resource")
    return validate_alpha97_data(json.loads(path.read_text(encoding="utf-8")))


def translator_base(
    alpha_resource: Path,
    alpha_sha256: str,
    output: Path,
    start: int,
    end: int,
    predecessor: Path,
    predecessor_sha256: str,
    module: str,
) -> list[str]:
    return [
        sys.executable,
        str(planner.TRANSLATOR),
        "--source", str(planner.SOURCE),
        "--source-sha256", planner.SOURCE_SHA256,
        "--endpoint", planner.ENDPOINT,
        "--start-ordinal", str(start),
        "--end-ordinal", str(end),
        "--alpha-frontier-resource", str(alpha_resource),
        "--alpha-frontier-sha256", alpha_sha256,
        "--output-dir", str(output),
        "--split-bytes", str(planner.SPLIT_BYTES),
        "--predecessor-resource", str(predecessor),
        "--predecessor-resource-sha256", predecessor_sha256,
        "--module-prefix", module,
        "--namespace", planner.NAMESPACE,
        "--wpp-profile", "WPP_PROFILE_V2",
    ]


def run_translator(command: Sequence[str]) -> str:
    require(Path(command[1]).resolve() == planner.TRANSLATOR.resolve(),
            "refusing to execute anything except the pinned source translator")
    completed = subprocess.run(
        list(command),
        cwd=HERE,
        text=True,
        encoding="utf-8",
        capture_output=True,
        check=False,
    )
    require(
        completed.returncode == 0,
        "source translator failed with exit code "
        f"{completed.returncode}:\n{completed.stdout}\n{completed.stderr}",
    )
    require(not completed.stderr.strip(),
            f"source translator produced stderr: {completed.stderr}")
    return completed.stdout


def resolve_resource_path(value: Any, resource: Path, description: str) -> Path:
    require(isinstance(value, str) and value, f"missing {description} path")
    path = Path(value)
    if not path.is_absolute():
        path = resource.parent / path
    return path.resolve()


def verify_preflight(
    resource: Path,
    alpha_resource: Path,
    alpha_sha256: str,
    plan: Mapping[str, Any],
) -> dict[str, Any]:
    require(resource.is_file(), "translator did not publish the alpha97 preflight")
    data = json.loads(resource.read_text(encoding="utf-8"))
    require(data.get("status") == "PASS_SOURCE_ONLY_PREFLIGHT",
            "full-interval translator preflight did not pass")
    require(data.get("mode") == "audit-only", "preflight is not audit-only")
    audit = data.get("sourceAudit")
    require(isinstance(audit, Mapping), "preflight has no embedded source audit")
    remaining = plan["remainingInterval"]
    require(
        audit.get("leanStartedByThisProducer") is False
        and audit.get("sourceSha256") == planner.SOURCE_SHA256
        and audit.get("endpoint") == planner.ENDPOINT
        and audit.get("endpointAst") == planner.ENDPOINT_AST
        and audit.get("closureProofTheoremCount") == planner.CLOSURE_THEOREM_COUNT
        and audit.get("startTheoremOrdinal") == remaining["startTheoremOrdinal"]
        and audit.get("endTheoremOrdinal") == remaining["endTheoremOrdinal"]
        and audit.get("selectedTheoremCount") == remaining["theoremCount"]
        and canonical_json_sha256(audit.get("selectedLabels"))
            == remaining["selectedLabelsSha256"]
        and audit.get("selectedProofOpsMapSha256")
            == remaining["selectedProofOpsMapSha256"],
        "full-interval preflight differs from the frozen closure plan",
    )
    frontier = audit.get("alphaFrontier")
    require(isinstance(frontier, Mapping), "preflight has no alpha frontier record")
    require(
        Path(str(frontier.get("resource"))).resolve() == alpha_resource.resolve()
        and frontier.get("resourceSha256") == alpha_sha256
        and frontier.get("endOrdinal") == 97,
        "preflight used a different alpha frontier",
    )
    coverage = audit.get("coverage")
    require(
        isinstance(coverage, Mapping)
        and coverage.get("allSelectedLeavesCovered") is True
        and coverage.get("unsupportedLeaves") == [],
        "full remaining interval has unsupported leaves",
    )
    checks = audit.get("checks")
    require(isinstance(checks, Mapping) and all(value is True for value in checks.values()),
            "preflight did not satisfy every source-only check")
    return data


def verify_emission(
    resource: Path,
    chunk: Mapping[str, Any],
    alpha_resource: Path,
    alpha_sha256: str,
    predecessor: Path,
    predecessor_sha256: str,
) -> dict[str, Any]:
    require(resource.is_file(), f"translator did not publish {resource}")
    data = json.loads(resource.read_text(encoding="utf-8"))
    require(
        data.get("status") == "PASS_SOURCE_ONLY_EMITTED_STRUCTURAL"
        and data.get("leanStartedByThisProducer") is False
        and data.get("sourceSha256") == planner.SOURCE_SHA256
        and data.get("endpoint") == planner.ENDPOINT
        and data.get("endpointAst") == planner.ENDPOINT_AST
        and data.get("closureProofTheoremCount") == planner.CLOSURE_THEOREM_COUNT
        and data.get("startTheoremOrdinal") == chunk["startTheoremOrdinal"]
        and data.get("endTheoremOrdinal") == chunk["endTheoremOrdinal"]
        and data.get("theoremCount") == chunk["theoremCount"]
        and data.get("maximumCopiedTheoremBytes") == planner.SPLIT_BYTES
        and data.get("genericDvFallbackCount") == 0
        and data.get("forbiddenGeneratedSourceTokens") == [],
        f"emitted chunk {chunk['chunkId']} differs from the frozen plan",
    )
    parts = data.get("parts")
    require(isinstance(parts, list) and parts, "emitted chunk has no Lean source parts")
    require(
        parts[0].get("firstLabel") == chunk["firstLabel"]
        and parts[-1].get("lastLabel") == chunk["lastLabel"],
        "emitted chunk boundary labels differ",
    )
    for part in parts:
        source = resolve_resource_path(part.get("source"), resource, "part source")
        require_hash(source, str(part.get("sourceSha256")), "generated part source")
        require(
            part.get("oversizedSingleton") is True
            or int(part.get("copiedTheoremBytes", -1)) <= planner.SPLIT_BYTES,
            "non-singleton generated part exceeds the byte limit",
        )
    umbrella = data.get("umbrellaModule")
    require(isinstance(umbrella, Mapping), "emitted chunk has no umbrella module")
    require(umbrella.get("module") == chunk["modulePrefix"],
            "emitted umbrella module differs")
    umbrella_source = resolve_resource_path(
        umbrella.get("source"), resource, "umbrella source"
    )
    require_hash(
        umbrella_source, str(umbrella.get("sourceSha256")), "generated umbrella source"
    )
    frontier = data.get("alphaFrontier")
    require(isinstance(frontier, Mapping), "emitted chunk has no alpha frontier record")
    require(
        Path(str(frontier.get("resource"))).resolve() == alpha_resource.resolve()
        and frontier.get("resourceSha256") == alpha_sha256
        and frontier.get("endOrdinal") == 97,
        "emitted chunk used a different alpha frontier",
    )
    pred = data.get("predecessor")
    require(isinstance(pred, Mapping), "emitted chunk has no predecessor record")
    require(
        Path(str(pred.get("resource"))).resolve() == predecessor.resolve()
        and pred.get("resourceSha256") == predecessor_sha256,
        "emitted chunk used a different predecessor",
    )
    source_audit_record = data.get("sourceAudit")
    require(isinstance(source_audit_record, Mapping), "chunk has no source-audit pin")
    source_audit = resolve_resource_path(
        source_audit_record.get("path"), resource, "chunk source audit"
    )
    require_hash(
        source_audit,
        str(source_audit_record.get("sha256")),
        "generated chunk source audit",
    )
    audit = json.loads(source_audit.read_text(encoding="utf-8"))
    require(
        canonical_json_sha256(audit.get("selectedLabels"))
            == chunk["selectedLabelsSha256"]
        and audit.get("selectedProofOpsMapSha256")
            == chunk["selectedProofOpsMapSha256"],
        "generated chunk labels/proof programs differ from the frozen plan",
    )
    checks = audit.get("checks")
    require(isinstance(checks, Mapping) and all(value is True for value in checks.values()),
            "generated chunk did not satisfy every translator check")
    coverage = audit.get("coverage")
    require(
        isinstance(coverage, Mapping)
        and coverage.get("allSelectedLeavesCovered") is True
        and coverage.get("unsupportedLeaves") == [],
        "generated chunk has unsupported leaves",
    )
    return data


def publish_session(path: Path, value: object) -> None:
    require(path.parent.is_dir(), f"session resource parent does not exist: {path.parent}")
    require(not path.exists(), f"refusing to overwrite session resource: {path}")
    staging = path.parent / f".{path.name}.staging-v1"
    require(not staging.exists(), f"stale session staging file exists: {staging}")
    content = json_bytes(value)
    staging.write_bytes(content)
    require(staging.read_bytes() == content, "session staging write changed")
    staging.replace(path)
    require(path.read_bytes() == content, "published session resource changed")


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--alpha-frontier-resource", type=Path, required=True)
    parser.add_argument("--alpha-frontier-sha256", required=True)
    parser.add_argument("--output-parent", type=Path, required=True)
    parser.add_argument("--session-resource", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    alpha_resource = args.alpha_frontier_resource.resolve()
    alpha_sha256 = normalized_sha256(
        args.alpha_frontier_sha256, "alpha97 resource"
    )
    output_parent = args.output_parent.resolve()
    session_resource = args.session_resource.resolve()
    require(output_parent.is_dir(), f"output parent does not exist: {output_parent}")
    require(session_resource.parent.is_dir(),
            f"session resource parent does not exist: {session_resource.parent}")
    plan = load_plan()
    load_alpha97_resource(alpha_resource, alpha_sha256)

    preflight_dir = output_parent / PREFLIGHT_DIRECTORY
    outputs = [output_parent / chunk["outputDirectory"] for chunk in plan["chunks"]]
    for path in [preflight_dir, *outputs]:
        require(not path.exists(), f"refusing to overwrite append-only output: {path}")
        staging = path.parent / f".{path.name}.staging-v1"
        require(not staging.exists(), f"stale translator staging directory: {staging}")
    require(not session_resource.exists(),
            f"refusing to overwrite session resource: {session_resource}")

    preflight_command = translator_base(
        alpha_resource,
        alpha_sha256,
        preflight_dir,
        planner.REMAINING_START,
        planner.REMAINING_END,
        planner.PREDECESSOR_RESOURCE,
        planner.PREDECESSOR_RESOURCE_SHA256,
        PREFLIGHT_MODULE,
    ) + ["--audit-only"]
    preflight_stdout = run_translator(preflight_command)
    preflight_resource = preflight_dir / "resource.json"
    verify_preflight(
        preflight_resource, alpha_resource, alpha_sha256, plan
    )

    predecessor = planner.PREDECESSOR_RESOURCE.resolve()
    predecessor_sha256 = planner.PREDECESSOR_RESOURCE_SHA256
    records: list[dict[str, object]] = []
    for chunk, output in zip(plan["chunks"], outputs):
        command = translator_base(
            alpha_resource,
            alpha_sha256,
            output,
            int(chunk["startTheoremOrdinal"]),
            int(chunk["endTheoremOrdinal"]),
            predecessor,
            predecessor_sha256,
            str(chunk["modulePrefix"]),
        )
        stdout = run_translator(command)
        resource = output / "resource.json"
        verify_emission(
            resource,
            chunk,
            alpha_resource,
            alpha_sha256,
            predecessor,
            predecessor_sha256,
        )
        resource_sha256 = sha256(resource)
        records.append(
            {
                "chunkId": chunk["chunkId"],
                "startTheoremOrdinal": chunk["startTheoremOrdinal"],
                "endTheoremOrdinal": chunk["endTheoremOrdinal"],
                "module": chunk["modulePrefix"],
                "resource": str(resource),
                "resourceSha256": resource_sha256,
                "translatorStdout": stdout,
            }
        )
        predecessor = resource.resolve()
        predecessor_sha256 = resource_sha256

    session = {
        "schema": "nf-wpp-remaining-replay-source-session-v1",
        "status": (
            "PASS_SOURCE_ONLY_REMAINING_REPLAY_EMITTED_ALPHA97_ACCEPTED_"
            "KERNEL_VERIFICATION_SEPARATE"
        ),
        "leanStartedByRunner": False,
        "plan": str(PLAN),
        "planSha256": PLAN_SHA256,
        "releaseId": "NF_WPP_TRANSLATOR_TOOLCHAIN_002",
        "translator": str(planner.TRANSLATOR),
        "translatorSha256": planner.TRANSLATOR_SHA256,
        "alphaFrontierResource": str(alpha_resource),
        "alphaFrontierResourceSha256": alpha_sha256,
        "alphaFrontierEndOrdinal": 97,
        "preflight": {
            "resource": str(preflight_resource),
            "resourceSha256": sha256(preflight_resource),
            "translatorStdout": preflight_stdout,
        },
        "chunks": records,
        "final": {
            "endTheoremOrdinal": planner.REMAINING_END,
            "label": planner.ENDPOINT,
            "ast": planner.ENDPOINT_AST,
            "module": plan["chunks"][-1]["modulePrefix"],
            "sourceResource": str(predecessor),
            "sourceResourceSha256": predecessor_sha256,
        },
        "kernelVerificationSeparate": True,
    }
    publish_session(session_resource, session)
    print(
        "PASS source-only remaining replay: 1455 theorems, 7 chunks, "
        f"final resource {predecessor_sha256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
