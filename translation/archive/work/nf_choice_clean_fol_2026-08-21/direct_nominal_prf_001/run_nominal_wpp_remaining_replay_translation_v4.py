#!/usr/bin/env python3
"""Hardened capture-safe Release004 replay for WPP ordinals 2867--4321.

This immutable successor pins the v3 launcher, hardened v3 alpha adapter, and
the runtime plan-builder module used by the frozen replay implementation.  It
publishes the frozen source replay unchanged, then publishes a separate
session envelope recording this launcher's complete provenance.  No Lean
process is invoked.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Sequence


HERE = Path(__file__).resolve().parent
PYTHON_SHA256 = "D8E3F0ADF246DB00358C0C4ED349CF714898178F9558FB0E944F79F5C07F8EAA"
PREDECESSOR_RUNNER = HERE / "run_nominal_wpp_remaining_replay_translation_v3.py"
PREDECESSOR_RUNNER_SHA256 = "03BF149243BF96E08CBF083F36A024E48E4DD4DA15F70BB8182438A16239E258"
ADAPTER = HERE / "adapt_release004_alpha_frontier_for_replay_v3.py"
ADAPTER_SHA256 = "EFBDF43A4C8AE9D5D6D9A9170D0AE2DC99426704D0FF5575AE0910EF2085DA63"
ADAPTER_SCHEMA = "nf-release004-capture-safe-alpha-frontier-replay-adapter-v3"
PLANNER = HERE / "build_nominal_wpp_remaining_replay_plan_v1.py"
PLANNER_SHA256 = "98E3E87E97F9B67E5501BC207B8CF1CC284EB96E1B7303C767C5CC2A60C1D2C9"
TRANSLATOR = HERE / "reusable_nominal_mm_translator_v1.py"
TRANSLATOR_SHA256 = "8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94"
DEFAULT_ADAPTER_DIRECTORY = "nominal_alpha97_capture_safe_hardened_replay_adapter_001"
EXPECTED_CHUNKS = ["012B", "013", "014", "015", "016", "017", "018"]


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
    require(actual == expected.upper(), f"{description} hash mismatch: {actual}")


def load_module(path: Path, name: str) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None,
            f"could not load pinned module: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_runtime_planner(legacy: ModuleType) -> None:
    require_hash(PLANNER, PLANNER_SHA256,
                 "remaining-replay runtime planner")
    require_hash(TRANSLATOR, TRANSLATOR_SHA256,
                 "remaining-replay source translator")
    planner = getattr(legacy, "planner", None)
    planner_file = getattr(planner, "__file__", None)
    require(isinstance(planner_file, str)
            and Path(planner_file).resolve() == PLANNER.resolve(),
            "frozen replay imported a different runtime planner")
    planner_translator = getattr(planner, "TRANSLATOR", None)
    require(planner_translator is not None
            and Path(planner_translator).resolve() == TRANSLATOR.resolve(),
            "runtime planner selected a different translator")
    require(getattr(planner, "TRANSLATOR_SHA256", None) == TRANSLATOR_SHA256,
            "runtime planner translator hash authority changed")


def load_pinned_modules() -> tuple[ModuleType, ModuleType, ModuleType]:
    require_hash(Path(sys.executable).resolve(), PYTHON_SHA256,
                 "Python interpreter")
    require_hash(PREDECESSOR_RUNNER, PREDECESSOR_RUNNER_SHA256,
                 "capture-safe remaining-replay runner v3")
    require_hash(ADAPTER, ADAPTER_SHA256,
                 "hardened capture-safe alpha adapter v3")
    # Pin the module before loading the predecessor that imports it; this
    # prevents unvalidated planner top-level code from running first.
    require_hash(PLANNER, PLANNER_SHA256,
                 "remaining-replay runtime planner")
    require_hash(TRANSLATOR, TRANSLATOR_SHA256,
                 "remaining-replay source translator")
    preloaded = sys.modules.get("build_nominal_wpp_remaining_replay_plan_v1")
    if preloaded is not None:
        preloaded_file = getattr(preloaded, "__file__", None)
        require(isinstance(preloaded_file, str)
                and Path(preloaded_file).resolve() == PLANNER.resolve(),
                "a different runtime planner was already imported")
    predecessor = load_module(
        PREDECESSOR_RUNNER, "_remaining_replay_runner_v3_frozen"
    )
    _old_adapter, legacy, _v2_runner = predecessor.load_pinned_modules()
    validate_runtime_planner(legacy)
    adapter = load_module(ADAPTER, "_capture_safe_alpha_replay_adapter_v3")
    return adapter, legacy, predecessor


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--alpha-frontier-resource", type=Path, required=True)
    result.add_argument("--alpha-frontier-sha256", required=True)
    result.add_argument("--output-parent", type=Path, required=True)
    result.add_argument("--session-resource", type=Path, required=True)
    result.add_argument("--frozen-session-resource", type=Path)
    result.add_argument("--adapter-output-dir", type=Path)
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    adapter, legacy, _predecessor = load_pinned_modules()
    runner = Path(__file__).resolve()
    runner_hash = sha256(runner)
    output_parent = args.output_parent.resolve()
    session_resource = args.session_resource.resolve()
    alpha_resource = args.alpha_frontier_resource.resolve()
    frozen_session = (
        args.frozen_session_resource.resolve()
        if args.frozen_session_resource is not None
        else session_resource.with_name(
            f"{session_resource.stem}.frozen-v1{session_resource.suffix}"
        )
    )
    require(output_parent.is_dir(),
            f"output parent does not exist: {output_parent}")
    require(session_resource.parent.is_dir(),
            f"session parent does not exist: {session_resource.parent}")
    require(frozen_session.parent.is_dir(),
            f"frozen-session parent does not exist: {frozen_session.parent}")
    require(frozen_session != session_resource,
            "frozen and provenance session resources must differ")
    require(not session_resource.exists(),
            f"refusing to overwrite session resource: {session_resource}")
    require(not frozen_session.exists(),
            f"refusing to overwrite frozen session: {frozen_session}")
    for session_path in (session_resource, frozen_session):
        require(
            not (session_path.parent / f".{session_path.name}.staging-v1").exists(),
            f"stale session staging file exists: {session_path}",
        )
    plan: dict[str, Any] = legacy.load_plan()
    chunks = plan.get("chunks")
    require(
        isinstance(chunks, list)
        and [chunk.get("chunkId") for chunk in chunks] == EXPECTED_CHUNKS,
        "runtime plan does not contain exact replay chunks C12B through C18",
    )
    adapter_dir = (
        args.adapter_output_dir.resolve()
        if args.adapter_output_dir is not None
        else output_parent / DEFAULT_ADAPTER_DIRECTORY
    )
    require(adapter_dir.parent.is_dir(),
            f"adapter output parent does not exist: {adapter_dir.parent}")
    require(not adapter_dir.exists(),
            f"refusing to overwrite alpha adapter: {adapter_dir}")
    future_outputs = [
        output_parent / legacy.PREFLIGHT_DIRECTORY,
        *(output_parent / chunk["outputDirectory"] for chunk in chunks),
    ]
    for output in future_outputs:
        require(not output.exists(),
                f"refusing to overwrite append-only output: {output}")
        require(not (output.parent / f".{output.name}.staging-v1").exists(),
                f"stale translator staging directory: {output}")

    preview = adapter.build_adapter(
        alpha_resource, args.alpha_frontier_sha256
    )
    require(
        preview.get("schema") == ADAPTER_SCHEMA
        and preview.get("firstUsePrefix", {}).get("endOrdinal") == 97,
        "hardened capture-safe alpha frontier does not end at exact ordinal 97",
    )
    modules = preview.get("acceptedModules")
    require(
        isinstance(modules, list)
        and [row.get("ordinal") for row in modules] == list(range(49, 98))
        and preview.get("moduleOverrides") == modules,
        "hardened compatibility adapter has the wrong acceptedModules view",
    )
    chain = preview.get("captureSafeKernelChain")
    require(
        isinstance(chain, list)
        and [row.get("ordinal") for row in chain] == list(range(97, 87, -1)),
        "hardened compatibility adapter has the wrong kernel ancestry",
    )
    adapter_resource, adapter_sha = adapter.publish_adapter(
        alpha_resource, args.alpha_frontier_sha256, adapter_dir
    )
    accepted_adapter = json.loads(
        adapter_resource.read_text(encoding="utf-8")
    )
    legacy.validate_alpha97_data(accepted_adapter)

    result = legacy.main([
        "--alpha-frontier-resource", str(adapter_resource),
        "--alpha-frontier-sha256", adapter_sha,
        "--output-parent", str(output_parent),
        "--session-resource", str(frozen_session),
    ])
    require(result == 0, "frozen remaining-replay runner returned nonzero")
    frozen = json.loads(frozen_session.read_text(encoding="utf-8"))
    require(
        frozen.get("alphaFrontierResource") == str(adapter_resource.resolve())
        and frozen.get("alphaFrontierResourceSha256") == adapter_sha
        and frozen.get("alphaFrontierEndOrdinal") == 97,
        "frozen replay session did not use the exact compatibility adapter",
    )
    session = dict(frozen)
    session["launcherProvenance"] = {
        "schema": "nf-capture-safe-remaining-replay-launcher-provenance-v1",
        "sourceOnly": True,
        "leanInvokedByLauncher": False,
        "runner": str(runner),
        "runnerSha256": runner_hash,
        "predecessorRunner": str(PREDECESSOR_RUNNER),
        "predecessorRunnerSha256": PREDECESSOR_RUNNER_SHA256,
        "adapter": str(ADAPTER),
        "adapterSha256": ADAPTER_SHA256,
        "planner": str(PLANNER),
        "plannerSha256": PLANNER_SHA256,
        "translator": str(TRANSLATOR),
        "translatorSha256": TRANSLATOR_SHA256,
        "frozenSessionResource": str(frozen_session),
        "frozenSessionResourceSha256": sha256(frozen_session),
    }
    legacy.publish_session(session_resource, session)
    print(
        "PASS hardened capture-safe Release004 source replay; "
        f"adapter={adapter_sha} session={sha256(session_resource)} "
        f"runner={runner_hash} predecessorRunner={PREDECESSOR_RUNNER_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
