#!/usr/bin/env python3
"""Capture-safe Release004 source replay for WPP ordinals 2867--4321.

This append-only successor pins the accepted v2 replay launcher and all of its
frozen replay authorities.  It adapts an exact capture-safe global97 kernel
chain with the v2 frontier adapter, validates the resulting compatibility
schema with the frozen runner, and delegates the exact seven-chunk source
emission to the hash-pinned v1 replay implementation.  It never invokes Lean.
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
PREDECESSOR_RUNNER = HERE / "run_nominal_wpp_remaining_replay_translation_v2.py"
PREDECESSOR_RUNNER_SHA256 = "7673A51FC97516C990951B9C80A4CCAC7A8EE4CAB0DE69DF1C3EE85829C83751"
ADAPTER = HERE / "adapt_release004_alpha_frontier_for_replay_v2.py"
ADAPTER_SHA256 = "546B116AF94E136382B07D7795E3569DCDC54EAFC60A8719B742883D5C298116"
ADAPTER_SCHEMA = "nf-release004-capture-safe-alpha-frontier-replay-adapter-v2"
DEFAULT_ADAPTER_DIRECTORY = "nominal_alpha97_capture_safe_replay_adapter_001"


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


def load_pinned_modules() -> tuple[ModuleType, ModuleType, ModuleType]:
    require_hash(Path(sys.executable).resolve(), PYTHON_SHA256,
                 "Python interpreter")
    require_hash(PREDECESSOR_RUNNER, PREDECESSOR_RUNNER_SHA256,
                 "Release004 remaining-replay runner v2")
    require_hash(ADAPTER, ADAPTER_SHA256,
                 "capture-safe Release004 alpha adapter v2")
    predecessor = load_module(
        PREDECESSOR_RUNNER, "_remaining_replay_runner_v2_frozen"
    )
    # This performs the predecessor's own Python/adapter/plan/translator hash
    # checks and returns the exact frozen v1 replay implementation.
    _old_adapter, legacy = predecessor.load_pinned_modules()
    adapter = load_module(ADAPTER, "_capture_safe_alpha_replay_adapter_v2")
    return adapter, legacy, predecessor


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--alpha-frontier-resource", type=Path, required=True)
    result.add_argument("--alpha-frontier-sha256", required=True)
    result.add_argument("--output-parent", type=Path, required=True)
    result.add_argument("--session-resource", type=Path, required=True)
    result.add_argument("--adapter-output-dir", type=Path)
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    adapter, legacy, predecessor = load_pinned_modules()
    output_parent = args.output_parent.resolve()
    session_resource = args.session_resource.resolve()
    alpha_resource = args.alpha_frontier_resource.resolve()
    require(output_parent.is_dir(),
            f"output parent does not exist: {output_parent}")
    require(session_resource.parent.is_dir(),
            f"session parent does not exist: {session_resource.parent}")
    plan: dict[str, Any] = legacy.load_plan()
    adapter_dir = (
        args.adapter_output_dir.resolve()
        if args.adapter_output_dir is not None
        else output_parent / DEFAULT_ADAPTER_DIRECTORY
    )
    require(adapter_dir.parent.is_dir(),
            f"adapter output parent does not exist: {adapter_dir.parent}")
    require(not adapter_dir.exists(),
            f"refusing to overwrite alpha adapter: {adapter_dir}")
    require(not session_resource.exists(),
            f"refusing to overwrite session resource: {session_resource}")
    future_outputs = [
        output_parent / legacy.PREFLIGHT_DIRECTORY,
        *(output_parent / chunk["outputDirectory"] for chunk in plan["chunks"]),
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
        "capture-safe Release004 alpha frontier does not end at exact ordinal 97",
    )
    modules = preview.get("acceptedModules")
    require(
        isinstance(modules, list)
        and [row.get("ordinal") for row in modules] == list(range(49, 98))
        and preview.get("moduleOverrides") == modules,
        "capture-safe compatibility adapter has the wrong acceptedModules view",
    )
    chain = preview.get("captureSafeKernelChain")
    require(
        isinstance(chain, list)
        and [row.get("ordinal") for row in chain] == list(range(97, 87, -1)),
        "capture-safe compatibility adapter has the wrong kernel ancestry",
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
        "--session-resource", str(session_resource),
    ])
    require(result == 0, "frozen remaining-replay runner returned nonzero")
    session = json.loads(session_resource.read_text(encoding="utf-8"))
    require(
        session.get("alphaFrontierResource") == str(adapter_resource.resolve())
        and session.get("alphaFrontierResourceSha256") == adapter_sha
        and session.get("alphaFrontierEndOrdinal") == 97,
        "published replay session did not use the exact compatibility adapter",
    )
    print(
        "PASS capture-safe Release004 source replay; "
        f"adapter={adapter_sha} session={sha256(session_resource)} "
        f"predecessorRunner={predecessor.PYTHON_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
