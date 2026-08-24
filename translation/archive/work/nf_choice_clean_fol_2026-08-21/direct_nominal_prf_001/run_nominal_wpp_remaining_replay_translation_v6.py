#!/usr/bin/env python3
"""Regenerate frozen C17--C18 with translator v3, source-only.

This append-only successor validates the exact v5 source session, the complete
accepted v1 prefix (preflight and C12B--C16), the hardened alpha97 adapter, and
the frozen plan before switching only the C17--C18 producer to translator v3.
It writes fresh output directories and atomically publishes a fresh session.
It never invokes Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Mapping, Sequence


HERE = Path(__file__).resolve().parent
THIS = Path(__file__).resolve()
PYTHON_SHA256 = "D8E3F0ADF246DB00358C0C4ED349CF714898178F9558FB0E944F79F5C07F8EAA"
PREDECESSOR_RUNNER = HERE / "run_nominal_wpp_remaining_replay_translation_v5.py"
PREDECESSOR_RUNNER_SHA256 = (
    "A8768CF97776222CD68A128327FCD380222787CD4D2369C1FB29D5BF1D134D21"
)
PREDECESSOR_SESSION = HERE / "nominal_wpp_remaining_replay_session_001.json"
PREDECESSOR_SESSION_SHA256 = (
    "44A06AAF07B09E86E9C06F41BCE0E7856137C05749A9307B55632720B28AB665"
)
SESSION_RESOURCE = HERE / "nominal_wpp_remaining_replay_session_002.json"
TRANSLATOR_V1 = HERE / "reusable_nominal_mm_translator_v1.py"
TRANSLATOR_V1_SHA256 = (
    "8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94"
)
TRANSLATOR_V2 = HERE / "reusable_nominal_mm_translator_v2.py"
TRANSLATOR_V2_SHA256 = (
    "52ED85A33329D1D4CE0E9D05622F74917E1CD9662959AAD7D7B6175244F34615"
)
TRANSLATOR_V3 = HERE / "reusable_nominal_mm_translator_v3.py"
TRANSLATOR_V3_SHA256 = (
    "DECC5089EAB55B95806EB74742FD47A1EB127502B243811DD882737FCB98475F"
)
OLD_V2_SUFFIX = {
    "017": (
        HERE / "reusable_nominal_mm_translator_v1_chunk017_compact_001"
        / "resource.json",
        "3CDA8DDFF3EF66C2AF8A31CB34FD18DD213051BAA49D7E2C788ED81E1E36B027",
    ),
    "018": (
        HERE / "reusable_nominal_mm_translator_v1_chunk018_compact_001"
        / "resource.json",
        "6C7387199F62829B4B309AB18E811CC1EE299D22E09A5EA71A98F2C69FBF1E7D",
    ),
}
V3_SUFFIX_OUTPUTS = {
    "017": "reusable_nominal_mm_translator_v3_chunk017_compact_001",
    "018": "reusable_nominal_mm_translator_v3_chunk018_compact_001",
}
EXPECTED_CHUNKS = ["012B", "013", "014", "015", "016", "017", "018"]
V1_PREFIX_END_ORDINAL = 4_004


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def require_hash(path: Path, expected: str, description: str) -> None:
    require(path.is_file(), f"missing {description}: {path}")
    actual = sha256(path)
    require(actual == expected, f"{description} hash mismatch: {actual}")


def load_module(path: Path, name: str) -> ModuleType:
    require(name not in sys.modules, f"module name already loaded: {name}")
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None,
            f"could not load pinned module: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"JSON root is not an object: {path}")
    return value


def load_authorities() -> tuple[
    ModuleType, ModuleType, ModuleType, ModuleType, ModuleType
]:
    require_hash(Path(sys.executable).resolve(), PYTHON_SHA256,
                 "Python interpreter")
    require_hash(PREDECESSOR_RUNNER, PREDECESSOR_RUNNER_SHA256,
                 "v5 replay launcher")
    require_hash(PREDECESSOR_SESSION, PREDECESSOR_SESSION_SHA256,
                 "v5 source session")
    require_hash(TRANSLATOR_V1, TRANSLATOR_V1_SHA256,
                 "accepted translator v1")
    require_hash(TRANSLATOR_V2, TRANSLATOR_V2_SHA256,
                 "superseded translator v2")
    require_hash(TRANSLATOR_V3, TRANSLATOR_V3_SHA256,
                 "FV-deduplicating translator v3")
    v5 = load_module(PREDECESSOR_RUNNER, "_remaining_replay_runner_v5_for_v6")
    require(
        Path(v5.TRANSLATOR_V1).resolve() == TRANSLATOR_V1.resolve()
        and v5.TRANSLATOR_V1_SHA256 == TRANSLATOR_V1_SHA256
        and Path(v5.TRANSLATOR_V2).resolve() == TRANSLATOR_V2.resolve()
        and v5.TRANSLATOR_V2_SHA256 == TRANSLATOR_V2_SHA256,
        "v5 translator boundary changed",
    )
    adapter, legacy, planner, predecessor = v5.load_authorities()
    require(
        Path(planner.TRANSLATOR).resolve() == TRANSLATOR_V1.resolve()
        and planner.TRANSLATOR_SHA256 == TRANSLATOR_V1_SHA256,
        "frozen planner did not begin at translator v1",
    )
    return v5, adapter, legacy, planner, predecessor


def validate_superseded_v2_session(v5: ModuleType) -> dict[str, object]:
    data = read_json(PREDECESSOR_SESSION)
    require(
        data.get("schema") == "nf-wpp-remaining-replay-source-session-v2"
        and data.get("status")
        == (
            "PASS_SOURCE_ONLY_REMAINING_REPLAY_RESUMED_V1_PREFIX_V2_SUFFIX_"
            "ALPHA97_ACCEPTED_KERNEL_VERIFICATION_SEPARATE"
        )
        and data.get("leanStartedByRunner") is False
        and data.get("kernelVerificationSeparate") is True,
        "v5 source session boundary changed",
    )
    boundary = data.get("translationBoundary")
    require(
        isinstance(boundary, Mapping)
        and boundary.get("v1EndTheoremOrdinal") == V1_PREFIX_END_ORDINAL
        and boundary.get("v2StartTheoremOrdinal")
        == V1_PREFIX_END_ORDINAL + 1
        and Path(str(boundary.get("v1Translator"))).resolve()
        == TRANSLATOR_V1.resolve()
        and boundary.get("v1TranslatorSha256") == TRANSLATOR_V1_SHA256
        and Path(str(boundary.get("v2Translator"))).resolve()
        == TRANSLATOR_V2.resolve()
        and boundary.get("v2TranslatorSha256") == TRANSLATOR_V2_SHA256,
        "v5 session translator boundary changed",
    )
    launcher = data.get("launcherProvenance")
    require(
        isinstance(launcher, Mapping)
        and Path(str(launcher.get("runner"))).resolve()
        == PREDECESSOR_RUNNER.resolve()
        and launcher.get("runnerSha256") == PREDECESSOR_RUNNER_SHA256,
        "v5 session launcher provenance changed",
    )
    chunks = data.get("chunks")
    require(
        isinstance(chunks, list)
        and [row.get("chunkId") for row in chunks] == EXPECTED_CHUNKS,
        "v5 session chunk sequence changed",
    )
    for record in chunks[5:]:
        chunk_id = str(record.get("chunkId"))
        expected_path, expected_sha = OLD_V2_SUFFIX[chunk_id]
        require_hash(expected_path, expected_sha,
                     f"superseded v2 chunk {chunk_id}")
        require(
            Path(str(record.get("resource"))).resolve()
            == expected_path.resolve()
            and record.get("resourceSha256") == expected_sha
            and Path(str(record.get("translator"))).resolve()
            == TRANSLATOR_V2.resolve()
            and record.get("translatorSha256") == TRANSLATOR_V2_SHA256,
            f"v5 session chunk {chunk_id} record changed",
        )
        resource = read_json(expected_path)
        v5.require_producer(
            resource, TRANSLATOR_V2, TRANSLATOR_V2_SHA256,
            f"superseded v2 chunk {chunk_id}",
        )
        audit_record = resource.get("sourceAudit")
        require(isinstance(audit_record, Mapping),
                f"superseded v2 chunk {chunk_id} source audit is missing")
        audit = Path(str(audit_record.get("path"))).resolve()
        require_hash(audit, str(audit_record.get("sha256")),
                     f"superseded v2 chunk {chunk_id} source audit")
        v5.require_producer(
            read_json(audit), TRANSLATOR_V2, TRANSLATOR_V2_SHA256,
            f"superseded v2 chunk {chunk_id} source audit",
        )
    return {
        "resource": str(PREDECESSOR_SESSION),
        "resourceSha256": PREDECESSOR_SESSION_SHA256,
        "runner": str(PREDECESSOR_RUNNER),
        "runnerSha256": PREDECESSOR_RUNNER_SHA256,
        "disposition": "superseded-after-C17-part012-kernel-rewrite-failure",
    }


def exact_v3_command(
    v5: ModuleType,
    legacy: ModuleType,
    chunk: Mapping[str, Any],
    output: Path,
    predecessor: Path,
    predecessor_sha: str,
) -> list[str]:
    command = legacy.translator_base(
        v5.ADAPTER_RESOURCE,
        v5.ADAPTER_RESOURCE_SHA256,
        output,
        int(chunk["startTheoremOrdinal"]),
        int(chunk["endTheoremOrdinal"]),
        predecessor,
        predecessor_sha,
        str(chunk["modulePrefix"]),
    )
    expected = [
        sys.executable,
        str(TRANSLATOR_V3),
        "--source", str(legacy.planner.SOURCE),
        "--source-sha256", legacy.planner.SOURCE_SHA256,
        "--endpoint", legacy.planner.ENDPOINT,
        "--start-ordinal", str(chunk["startTheoremOrdinal"]),
        "--end-ordinal", str(chunk["endTheoremOrdinal"]),
        "--alpha-frontier-resource", str(v5.ADAPTER_RESOURCE),
        "--alpha-frontier-sha256", v5.ADAPTER_RESOURCE_SHA256,
        "--output-dir", str(output),
        "--split-bytes", str(legacy.planner.SPLIT_BYTES),
        "--predecessor-resource", str(predecessor),
        "--predecessor-resource-sha256", predecessor_sha,
        "--module-prefix", str(chunk["modulePrefix"]),
        "--namespace", legacy.planner.NAMESPACE,
        "--wpp-profile", "WPP_PROFILE_V2",
    ]
    require(command == expected,
            f"chunk {chunk['chunkId']} v3 command changed")
    return command


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--alpha-frontier-resource", type=Path, required=True)
    result.add_argument("--alpha-frontier-sha256", required=True)
    result.add_argument("--output-parent", type=Path, required=True)
    result.add_argument("--session-resource", type=Path, required=True)
    result.add_argument(
        "--validate-only",
        action="store_true",
        help=(
            "validate all frozen authorities, the v5 session, accepted v1 "
            "prefix, and exact v3 C17--C18 commands without starting a "
            "translator or publishing an artifact"
        ),
    )
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    output_parent = args.output_parent.resolve()
    session_resource = args.session_resource.resolve()
    alpha_resource = args.alpha_frontier_resource.resolve()
    alpha_sha = args.alpha_frontier_sha256.upper()
    require(output_parent == HERE,
            "v3 regeneration output parent must be the pinned directory")
    require(session_resource == SESSION_RESOURCE.resolve(),
            "v3 regeneration requires the exact session_002 destination")
    require(
        alpha_resource
        == (HERE / "h5g097coalesce3k001" / "resource.json").resolve()
        and alpha_sha
        == "6A5C3920E7A1098E45DCF50661BCA62477EC58F62966EF17D0B73C406A7FEFB9",
        "v3 regeneration requires the exact accepted global97 resource",
    )
    require_hash(alpha_resource, alpha_sha, "accepted global97 resource")
    require(not session_resource.exists(),
            f"refusing to overwrite session: {session_resource}")
    session_staging = (
        session_resource.parent / f".{session_resource.name}.staging-v1"
    )
    require(not session_staging.exists(),
            f"stale session staging file: {session_staging}")

    v5, adapter, legacy, planner, _predecessor = load_authorities()
    plan: dict[str, Any] = legacy.load_plan()
    chunks = plan.get("chunks")
    require(
        isinstance(chunks, list)
        and [row.get("chunkId") for row in chunks] == EXPECTED_CHUNKS,
        "frozen plan does not contain exact chunks C12B through C18",
    )
    v5.validate_adapter(adapter, legacy, alpha_resource, alpha_sha)
    records, predecessor, predecessor_sha, preflight_record = (
        v5.validate_v1_prefix(legacy, plan, output_parent)
    )
    superseded_session = validate_superseded_v2_session(v5)

    successor_chunks = chunks[5:]
    successor_outputs = [
        output_parent / V3_SUFFIX_OUTPUTS[str(chunk["chunkId"])]
        for chunk in successor_chunks
    ]
    for output in successor_outputs:
        require(not output.exists(),
                f"refusing to overwrite v3 successor output: {output}")
        staging = output.parent / f".{output.name}.staging-v1"
        require(not staging.exists(),
                f"stale v3 successor staging directory: {staging}")

    require(
        Path(planner.TRANSLATOR).resolve() == TRANSLATOR_V1.resolve()
        and planner.TRANSLATOR_SHA256 == TRANSLATOR_V1_SHA256,
        "planner translator changed before the v3 boundary",
    )
    planner.TRANSLATOR = TRANSLATOR_V3
    planner.TRANSLATOR_SHA256 = TRANSLATOR_V3_SHA256

    if args.validate_only:
        validation_predecessor = predecessor
        validation_sha = predecessor_sha
        for chunk, output in zip(successor_chunks, successor_outputs):
            exact_v3_command(
                v5, legacy, chunk, output,
                validation_predecessor, validation_sha,
            )
            validation_predecessor = output / "resource.json"
            validation_sha = "0" * 64
        require(
            not session_resource.exists()
            and all(not output.exists() for output in successor_outputs),
            "validate-only mode published an artifact",
        )
        print(
            "PASS validate-only v3 regeneration C17--C18; "
            "no translator process started and no artifact published"
        )
        return 0

    for chunk, output in zip(successor_chunks, successor_outputs):
        command = exact_v3_command(
            v5, legacy, chunk, output, predecessor, predecessor_sha
        )
        stdout = legacy.run_translator(command)
        resource = output / "resource.json"
        data = legacy.verify_emission(
            resource, chunk,
            v5.ADAPTER_RESOURCE, v5.ADAPTER_RESOURCE_SHA256,
            predecessor, predecessor_sha,
        )
        v5.require_producer(
            data, TRANSLATOR_V3, TRANSLATOR_V3_SHA256,
            f"chunk {chunk['chunkId']}",
        )
        audit = Path(str(data["sourceAudit"]["path"])).resolve()
        v5.require_producer(
            read_json(audit), TRANSLATOR_V3, TRANSLATOR_V3_SHA256,
            f"chunk {chunk['chunkId']} source audit",
        )
        resource_sha = sha256(resource)
        records.append({
            "chunkId": chunk["chunkId"],
            "startTheoremOrdinal": chunk["startTheoremOrdinal"],
            "endTheoremOrdinal": chunk["endTheoremOrdinal"],
            "module": chunk["modulePrefix"],
            "resource": str(resource.resolve()),
            "resourceSha256": resource_sha,
            "translator": str(TRANSLATOR_V3),
            "translatorSha256": TRANSLATOR_V3_SHA256,
            "publicationState": "new-v3-successor",
            "translatorStdout": stdout,
        })
        predecessor = resource.resolve()
        predecessor_sha = resource_sha

    runner_hash = sha256(THIS)
    session = {
        "schema": "nf-wpp-remaining-replay-source-session-v3",
        "status": (
            "PASS_SOURCE_ONLY_REMAINING_REPLAY_REGENERATED_V1_PREFIX_V3_"
            "SUFFIX_ALPHA97_ACCEPTED_KERNEL_VERIFICATION_SEPARATE"
        ),
        "leanStartedByRunner": False,
        "plan": str(v5.PLAN),
        "planSha256": v5.PLAN_SHA256,
        "planner": str(v5.PLANNER),
        "plannerSha256": v5.PLANNER_SHA256,
        "alphaFrontierResource": str(v5.ADAPTER_RESOURCE),
        "alphaFrontierResourceSha256": v5.ADAPTER_RESOURCE_SHA256,
        "alphaFrontierEndOrdinal": 97,
        "captureSafeKernelResource": str(alpha_resource),
        "captureSafeKernelResourceSha256": alpha_sha,
        "preflight": preflight_record,
        "supersededV2Session": superseded_session,
        "translationBoundary": {
            "v1EndTheoremOrdinal": V1_PREFIX_END_ORDINAL,
            "v3StartTheoremOrdinal": V1_PREFIX_END_ORDINAL + 1,
            "v1Translator": str(TRANSLATOR_V1),
            "v1TranslatorSha256": TRANSLATOR_V1_SHA256,
            "v2Translator": str(TRANSLATOR_V2),
            "v2TranslatorSha256": TRANSLATOR_V2_SHA256,
            "v3Translator": str(TRANSLATOR_V3),
            "v3TranslatorSha256": TRANSLATOR_V3_SHA256,
            "semanticChanges": [
                "identity-key definition-expansion cache inherited from v2",
                "exact duplicate applied root-FV rewrite emitted once",
            ],
            "metamathPlanChanged": False,
            "generatedLeanLanguageChanged": True,
        },
        "chunks": records,
        "final": {
            "endTheoremOrdinal": planner.REMAINING_END,
            "label": planner.ENDPOINT,
            "ast": planner.ENDPOINT_AST,
            "module": chunks[-1]["modulePrefix"],
            "sourceResource": str(predecessor),
            "sourceResourceSha256": predecessor_sha,
        },
        "launcherProvenance": {
            "schema": "nf-wpp-remaining-replay-resume-launcher-v2",
            "sourceOnly": True,
            "leanInvokedByLauncher": False,
            "runner": str(THIS),
            "runnerSha256": runner_hash,
            "predecessorRunner": str(PREDECESSOR_RUNNER),
            "predecessorRunnerSha256": PREDECESSOR_RUNNER_SHA256,
        },
        "kernelVerificationSeparate": True,
    }
    legacy.publish_session(session_resource, session)
    print(
        "PASS source-only v3 regeneration C17--C18; "
        f"session={sha256(session_resource)} final={predecessor_sha} "
        f"runner={runner_hash}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
