#!/usr/bin/env python3
"""Resume the frozen WPP source replay at C17 with translator v2.

This append-only successor validates the complete accepted v1 prefix
(preflight and C12B--C16), the hardened alpha97 adapter, and every frozen plan
authority before it changes the in-memory translator command from the pinned
v1 path to the hash-safe v2 successor.  It then emits only C17 and C18 and
atomically publishes a mixed-producer source session.  It never invokes Lean.
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
PREDECESSOR_RUNNER = HERE / "run_nominal_wpp_remaining_replay_translation_v4.py"
PREDECESSOR_RUNNER_SHA256 = "A5E541D025243544EA42B59D79713705CC3A4E15D64E802BE094CD82CD564363"
TRANSLATOR_V1 = HERE / "reusable_nominal_mm_translator_v1.py"
TRANSLATOR_V1_SHA256 = "8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94"
TRANSLATOR_V2 = HERE / "reusable_nominal_mm_translator_v2.py"
TRANSLATOR_V2_SHA256 = "52ED85A33329D1D4CE0E9D05622F74917E1CD9662959AAD7D7B6175244F34615"
PLANNER = HERE / "build_nominal_wpp_remaining_replay_plan_v1.py"
PLANNER_SHA256 = "98E3E87E97F9B67E5501BC207B8CF1CC284EB96E1B7303C767C5CC2A60C1D2C9"
PLAN = HERE / "nominal_wpp_remaining_replay_staging_001" / "plan.json"
PLAN_SHA256 = "F60772608E3074F98822234D8A541E2C952764EB8D5566B08B159EBB864AB628"
ALPHA97_RESOURCE = HERE / "h5g097coalesce3k001" / "resource.json"
ALPHA97_RESOURCE_SHA256 = "6A5C3920E7A1098E45DCF50661BCA62477EC58F62966EF17D0B73C406A7FEFB9"
ADAPTER_RESOURCE = (
    HERE
    / "nominal_alpha97_capture_safe_hardened_replay_adapter_001"
    / "resource.json"
)
ADAPTER_RESOURCE_SHA256 = "0734B024E79B16AF57BB4EB5265E6E22FF9F9F9598B6CB0210837E221EBE6353"
PREFLIGHT_RESOURCE_SHA256 = "0858AD96C5510F99A13DA048AF6AB99DAE8DB88DA8326623326789F40B60EA7F"
PREFIX_RESOURCE_SHA256 = {
    "012B": "50C94A164BE05C21911E457DF1CC7C2C04C2AEB025532FB5B85D434525763DB3",
    "013": "9C9FB1FFCA87B04CE4C02BBCCA1C8CBBA955EA3F5A510D9A3B9E418BB66FDC38",
    "014": "A0A593C020477CD31D38B60C2160E5DAB4524A9ED6E64F099633F3970615633C",
    "015": "F6D1AB293F9194F6A0B1AB663E09D7C375EFB1C05680E35A49E59796C6864C54",
    "016": "231765097D145BF982A014B361E1126E76CCFCFF821A4690E45F5C1B297D0D96",
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


def require_producer(
    data: Mapping[str, Any], path: Path, digest: str, description: str
) -> None:
    producer = data.get("producer")
    require(isinstance(producer, Mapping), f"missing {description} producer")
    recorded = producer.get("path")
    require(
        isinstance(recorded, str)
        and Path(recorded).resolve() == path.resolve()
        and producer.get("sha256") == digest,
        f"{description} producer boundary changed",
    )
    require_hash(path, digest, f"{description} producer")


def load_authorities() -> tuple[ModuleType, ModuleType, ModuleType, ModuleType]:
    require_hash(Path(sys.executable).resolve(), PYTHON_SHA256,
                 "Python interpreter")
    require_hash(PREDECESSOR_RUNNER, PREDECESSOR_RUNNER_SHA256,
                 "failed full-replay predecessor v4")
    require_hash(TRANSLATOR_V1, TRANSLATOR_V1_SHA256,
                 "accepted translator v1")
    require_hash(TRANSLATOR_V2, TRANSLATOR_V2_SHA256,
                 "hash-safe translator v2")
    require_hash(PLANNER, PLANNER_SHA256, "frozen replay planner")
    require_hash(PLAN, PLAN_SHA256, "frozen replay plan")
    predecessor = load_module(
        PREDECESSOR_RUNNER, "_remaining_replay_runner_v4_for_v5"
    )
    adapter, legacy, _v3 = predecessor.load_pinned_modules()
    planner = legacy.planner
    require(
        Path(planner.__file__).resolve() == PLANNER.resolve()
        and Path(planner.TRANSLATOR).resolve() == TRANSLATOR_V1.resolve()
        and planner.TRANSLATOR_SHA256 == TRANSLATOR_V1_SHA256,
        "v4 did not expose the exact frozen v1 planner/translator authority",
    )
    return adapter, legacy, planner, predecessor


def validate_adapter(
    adapter: ModuleType, legacy: ModuleType,
    alpha_resource: Path, alpha_sha256: str,
) -> dict[str, Any]:
    require_hash(ADAPTER_RESOURCE, ADAPTER_RESOURCE_SHA256,
                 "published hardened alpha97 adapter")
    expected = adapter.json_bytes(
        adapter.build_adapter(alpha_resource, alpha_sha256)
    )
    require(ADAPTER_RESOURCE.read_bytes() == expected,
            "published adapter differs from a fresh hardened reconstruction")
    data = read_json(ADAPTER_RESOURCE)
    legacy.validate_alpha97_data(data)
    return data


def validate_v1_prefix(
    legacy: ModuleType, plan: Mapping[str, Any], output_parent: Path,
) -> tuple[list[dict[str, object]], Path, str, dict[str, object]]:
    preflight = output_parent / legacy.PREFLIGHT_DIRECTORY / "resource.json"
    require_hash(preflight, PREFLIGHT_RESOURCE_SHA256,
                 "accepted full-interval preflight")
    preflight_data = legacy.verify_preflight(
        preflight, ADAPTER_RESOURCE, ADAPTER_RESOURCE_SHA256, plan
    )
    audit = preflight_data.get("sourceAudit")
    require(isinstance(audit, Mapping), "preflight source audit is missing")
    require_producer(audit, TRANSLATOR_V1, TRANSLATOR_V1_SHA256,
                     "preflight")

    predecessor = legacy.planner.PREDECESSOR_RESOURCE.resolve()
    predecessor_sha = legacy.planner.PREDECESSOR_RESOURCE_SHA256
    records: list[dict[str, object]] = []
    chunks = plan["chunks"]
    require(isinstance(chunks, list), "frozen plan chunks are missing")
    for chunk in chunks[:5]:
        chunk_id = str(chunk["chunkId"])
        require(chunk_id in PREFIX_RESOURCE_SHA256,
                f"unexpected v1 prefix chunk: {chunk_id}")
        resource = output_parent / str(chunk["outputDirectory"]) / "resource.json"
        expected_sha = PREFIX_RESOURCE_SHA256[chunk_id]
        require_hash(resource, expected_sha, f"accepted chunk {chunk_id}")
        data = legacy.verify_emission(
            resource, chunk, ADAPTER_RESOURCE, ADAPTER_RESOURCE_SHA256,
            predecessor, predecessor_sha,
        )
        require_producer(data, TRANSLATOR_V1, TRANSLATOR_V1_SHA256,
                         f"chunk {chunk_id}")
        source_audit = Path(str(data["sourceAudit"]["path"])).resolve()
        require_producer(read_json(source_audit), TRANSLATOR_V1,
                         TRANSLATOR_V1_SHA256,
                         f"chunk {chunk_id} source audit")
        records.append({
            "chunkId": chunk_id,
            "startTheoremOrdinal": chunk["startTheoremOrdinal"],
            "endTheoremOrdinal": chunk["endTheoremOrdinal"],
            "module": chunk["modulePrefix"],
            "resource": str(resource.resolve()),
            "resourceSha256": expected_sha,
            "translator": str(TRANSLATOR_V1),
            "translatorSha256": TRANSLATOR_V1_SHA256,
            "publicationState": "accepted-existing-v1-prefix",
        })
        predecessor = resource.resolve()
        predecessor_sha = expected_sha
    require(records[-1]["endTheoremOrdinal"] == V1_PREFIX_END_ORDINAL,
            "accepted v1 prefix does not end at theorem ordinal 4004")
    return records, predecessor, predecessor_sha, {
        "resource": str(preflight.resolve()),
        "resourceSha256": PREFLIGHT_RESOURCE_SHA256,
        "translator": str(TRANSLATOR_V1),
        "translatorSha256": TRANSLATOR_V1_SHA256,
    }


def exact_successor_command(
    legacy: ModuleType, chunk: Mapping[str, Any], output: Path,
    predecessor: Path, predecessor_sha: str,
) -> list[str]:
    command = legacy.translator_base(
        ADAPTER_RESOURCE,
        ADAPTER_RESOURCE_SHA256,
        output,
        int(chunk["startTheoremOrdinal"]),
        int(chunk["endTheoremOrdinal"]),
        predecessor,
        predecessor_sha,
        str(chunk["modulePrefix"]),
    )
    expected = [
        sys.executable,
        str(TRANSLATOR_V2),
        "--source", str(legacy.planner.SOURCE),
        "--source-sha256", legacy.planner.SOURCE_SHA256,
        "--endpoint", legacy.planner.ENDPOINT,
        "--start-ordinal", str(chunk["startTheoremOrdinal"]),
        "--end-ordinal", str(chunk["endTheoremOrdinal"]),
        "--alpha-frontier-resource", str(ADAPTER_RESOURCE),
        "--alpha-frontier-sha256", ADAPTER_RESOURCE_SHA256,
        "--output-dir", str(output),
        "--split-bytes", str(legacy.planner.SPLIT_BYTES),
        "--predecessor-resource", str(predecessor),
        "--predecessor-resource-sha256", predecessor_sha,
        "--module-prefix", str(chunk["modulePrefix"]),
        "--namespace", legacy.planner.NAMESPACE,
        "--wpp-profile", "WPP_PROFILE_V2",
    ]
    require(
        command == expected,
        f"chunk {chunk['chunkId']} successor command changed",
    )
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
            "validate every frozen authority, accepted v1 prefix, and exact v2 "
            "successor command without emitting or publishing anything"
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
            "resume output parent must be the pinned direct-nominal directory")
    require(alpha_resource == ALPHA97_RESOURCE.resolve()
            and alpha_sha == ALPHA97_RESOURCE_SHA256,
            "resume requires the exact accepted coalesced global97 resource")
    require_hash(alpha_resource, alpha_sha, "accepted global97 resource")
    require(session_resource.parent == HERE,
            "session must be published beside the pinned replay artifacts")
    require(not session_resource.exists(),
            f"refusing to overwrite session resource: {session_resource}")
    session_staging = session_resource.parent / f".{session_resource.name}.staging-v1"
    require(not session_staging.exists(),
            f"stale session staging file exists: {session_staging}")

    adapter, legacy, planner, _predecessor = load_authorities()
    plan: dict[str, Any] = legacy.load_plan()
    chunks = plan.get("chunks")
    require(
        isinstance(chunks, list)
        and [row.get("chunkId") for row in chunks] == EXPECTED_CHUNKS,
        "frozen plan does not contain exact chunks C12B through C18",
    )
    validate_adapter(adapter, legacy, alpha_resource, alpha_sha)
    records, predecessor, predecessor_sha, preflight_record = (
        validate_v1_prefix(legacy, plan, output_parent)
    )

    successor_chunks = chunks[5:]
    successor_outputs = [
        output_parent / str(chunk["outputDirectory"])
        for chunk in successor_chunks
    ]
    for output in successor_outputs:
        require(not output.exists(),
                f"refusing to overwrite successor output: {output}")
        staging = output.parent / f".{output.name}.staging-v1"
        require(not staging.exists(),
                f"stale successor staging directory: {staging}")

    # The frozen planner must remain v1 while its plan is rebuilt and checked.
    # Only after that check do source-emission commands move to v2.
    require(Path(planner.TRANSLATOR).resolve() == TRANSLATOR_V1.resolve()
            and planner.TRANSLATOR_SHA256 == TRANSLATOR_V1_SHA256,
            "planner translator authority changed before resume boundary")
    planner.TRANSLATOR = TRANSLATOR_V2
    planner.TRANSLATOR_SHA256 = TRANSLATOR_V2_SHA256

    if args.validate_only:
        validation_predecessor = predecessor
        validation_predecessor_sha = predecessor_sha
        for chunk, output in zip(successor_chunks, successor_outputs):
            exact_successor_command(
                legacy, chunk, output,
                validation_predecessor, validation_predecessor_sha,
            )
            validation_predecessor = output / "resource.json"
            # The real digest is derived and checked after atomic C17
            # publication.  This sentinel is used only to check the exact C18
            # argv shape without starting either translator process.
            validation_predecessor_sha = "0" * 64
        print(
            "PASS validate-only replay resume C17--C18; "
            "no translator process started and no artifact published"
        )
        return 0

    for chunk, output in zip(successor_chunks, successor_outputs):
        command = exact_successor_command(
            legacy, chunk, output, predecessor, predecessor_sha
        )
        stdout = legacy.run_translator(command)
        resource = output / "resource.json"
        data = legacy.verify_emission(
            resource, chunk, ADAPTER_RESOURCE, ADAPTER_RESOURCE_SHA256,
            predecessor, predecessor_sha,
        )
        require_producer(data, TRANSLATOR_V2, TRANSLATOR_V2_SHA256,
                         f"chunk {chunk['chunkId']}")
        source_audit = Path(str(data["sourceAudit"]["path"])).resolve()
        require_producer(read_json(source_audit), TRANSLATOR_V2,
                         TRANSLATOR_V2_SHA256,
                         f"chunk {chunk['chunkId']} source audit")
        resource_sha = sha256(resource)
        records.append({
            "chunkId": chunk["chunkId"],
            "startTheoremOrdinal": chunk["startTheoremOrdinal"],
            "endTheoremOrdinal": chunk["endTheoremOrdinal"],
            "module": chunk["modulePrefix"],
            "resource": str(resource.resolve()),
            "resourceSha256": resource_sha,
            "translator": str(TRANSLATOR_V2),
            "translatorSha256": TRANSLATOR_V2_SHA256,
            "publicationState": "new-v2-successor",
            "translatorStdout": stdout,
        })
        predecessor = resource.resolve()
        predecessor_sha = resource_sha

    runner_hash = sha256(THIS)
    session = {
        "schema": "nf-wpp-remaining-replay-source-session-v2",
        "status": (
            "PASS_SOURCE_ONLY_REMAINING_REPLAY_RESUMED_V1_PREFIX_V2_SUFFIX_"
            "ALPHA97_ACCEPTED_KERNEL_VERIFICATION_SEPARATE"
        ),
        "leanStartedByRunner": False,
        "plan": str(PLAN),
        "planSha256": PLAN_SHA256,
        "planner": str(PLANNER),
        "plannerSha256": PLANNER_SHA256,
        "alphaFrontierResource": str(ADAPTER_RESOURCE),
        "alphaFrontierResourceSha256": ADAPTER_RESOURCE_SHA256,
        "alphaFrontierEndOrdinal": 97,
        "captureSafeKernelResource": str(alpha_resource),
        "captureSafeKernelResourceSha256": alpha_sha,
        "preflight": preflight_record,
        "translationBoundary": {
            "v1EndTheoremOrdinal": V1_PREFIX_END_ORDINAL,
            "v2StartTheoremOrdinal": V1_PREFIX_END_ORDINAL + 1,
            "v1Translator": str(TRANSLATOR_V1),
            "v1TranslatorSha256": TRANSLATOR_V1_SHA256,
            "v2Translator": str(TRANSLATOR_V2),
            "v2TranslatorSha256": TRANSLATOR_V2_SHA256,
            "semanticChange": "identity-key definition-expansion cache",
            "metamathPlanChanged": False,
            "generatedLeanLanguageChanged": False,
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
            "schema": "nf-wpp-remaining-replay-resume-launcher-v1",
            "sourceOnly": True,
            "leanInvokedByLauncher": False,
            "runner": str(THIS),
            "runnerSha256": runner_hash,
            "failedFullReplayPredecessor": str(PREDECESSOR_RUNNER),
            "failedFullReplayPredecessorSha256": PREDECESSOR_RUNNER_SHA256,
        },
        "kernelVerificationSeparate": True,
    }
    legacy.publish_session(session_resource, session)
    print(
        "PASS source-only replay resume C17--C18; "
        f"session={sha256(session_resource)} final={predecessor_sha} "
        f"runner={runner_hash}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
