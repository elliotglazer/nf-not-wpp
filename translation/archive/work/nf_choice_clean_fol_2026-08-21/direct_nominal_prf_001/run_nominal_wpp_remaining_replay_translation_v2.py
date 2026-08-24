#!/usr/bin/env python3
"""Release004-aware source-only translation of WPP ordinals 2867--4321.

This append-only successor preserves the frozen v1 theorem plan and translator.
It first converts the accepted Release004 alpha97 kernel resource into the
audited compatibility view required by the frozen alpha loader, then delegates
the exact seven-chunk source emission to the hash-pinned v1 runner.  It never
invokes Lean.
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
ADAPTER = HERE / "adapt_release004_alpha_frontier_for_replay_v1.py"
ADAPTER_SHA256 = "1EE1EA18512296B5604590B0C4E7EB7DB2622A32E1ED29407315B47D58BE6E70"
LEGACY_RUNNER = HERE / "run_nominal_wpp_remaining_replay_translation_v1.py"
LEGACY_RUNNER_SHA256 = "15659142C547B90496C0156351D57F6E3DA1E252801AF980260F3B5043141593"
PLAN = HERE / "nominal_wpp_remaining_replay_staging_001" / "plan.json"
PLAN_SHA256 = "F60772608E3074F98822234D8A541E2C952764EB8D5566B08B159EBB864AB628"
TRANSLATOR = HERE / "reusable_nominal_mm_translator_v1.py"
TRANSLATOR_SHA256 = "8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94"
DEFAULT_ADAPTER_DIRECTORY = "nominal_alpha97_release004_replay_adapter_001"


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
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None,
            f"could not load pinned module: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_pinned_modules() -> tuple[ModuleType, ModuleType]:
    require_hash(Path(sys.executable).resolve(), PYTHON_SHA256,
                 "Python interpreter")
    require_hash(ADAPTER, ADAPTER_SHA256, "Release004 alpha adapter")
    require_hash(LEGACY_RUNNER, LEGACY_RUNNER_SHA256,
                 "frozen remaining-replay runner")
    require_hash(PLAN, PLAN_SHA256, "frozen remaining-replay plan")
    require_hash(TRANSLATOR, TRANSLATOR_SHA256, "frozen source translator")
    adapter = load_module(ADAPTER, "_release004_alpha_replay_adapter_v1")
    legacy = load_module(LEGACY_RUNNER, "_remaining_replay_runner_v1")
    return adapter, legacy


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
    adapter, legacy = load_pinned_modules()
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
    require(preview["firstUsePrefix"]["endOrdinal"] == 97,
            "Release004 alpha frontier does not end at exact ordinal 97")
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
        "PASS Release004-aware source replay; "
        f"adapter={adapter_sha} session={sha256(session_resource)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
