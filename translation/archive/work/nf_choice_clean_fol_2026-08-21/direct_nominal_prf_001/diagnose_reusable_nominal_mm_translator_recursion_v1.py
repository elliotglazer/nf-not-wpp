#!/usr/bin/env python3
"""Source-only theorem-boundary tracer for the pinned nominal translator.

This diagnostic does not alter or copy the frozen translator.  It hash-checks
that translator, loads it in-process, and reports the exact theorem whose
emission raises ``RecursionError``.  It never invokes Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Sequence


HERE = Path(__file__).resolve().parent
PYTHON_SHA256 = "D8E3F0ADF246DB00358C0C4ED349CF714898178F9558FB0E944F79F5C07F8EAA"
TRANSLATOR = HERE / "reusable_nominal_mm_translator_v1.py"
TRANSLATOR_SHA256 = "8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94"


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


def load_translator() -> ModuleType:
    require_hash(Path(sys.executable).resolve(), PYTHON_SHA256,
                 "Python interpreter")
    require_hash(TRANSLATOR, TRANSLATOR_SHA256, "frozen translator v1")
    spec = importlib.util.spec_from_file_location(
        "_diagnosed_reusable_nominal_mm_translator_v1", TRANSLATOR
    )
    require(spec is not None and spec.loader is not None,
            "could not load frozen translator v1")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def install_theorem_trace(translator: ModuleType) -> None:
    original_build = translator.build_emitter_class

    def traced_build(backend: Any) -> type:
        emitter_class = original_build(backend)
        original_emit = emitter_class.emit_theorem
        original_normalize = emitter_class.normalize_recanon

        def tree_metrics(root: Any) -> tuple[int, int, str]:
            depths: dict[int, int] = {}
            nodes: dict[int, Any] = {}
            best_child: dict[int, int] = {}
            active: set[int] = set()
            stack: list[tuple[Any, bool]] = [(root, False)]
            while stack:
                node, exiting = stack.pop()
                key = id(node)
                nodes[key] = node
                if key in depths:
                    continue
                if exiting:
                    active.discard(key)
                    child_keys = [id(child) for child in node.args]
                    if child_keys:
                        child = max(child_keys, key=lambda value: depths[value])
                        best_child[key] = child
                        depths[key] = depths[child] + 1
                    else:
                        depths[key] = 1
                    continue
                require(key not in active, "cycle in supposedly immutable AST")
                active.add(key)
                stack.append((node, True))
                for child in reversed(node.args):
                    if id(child) not in depths:
                        stack.append((child, False))
            path: list[str] = []
            cursor = id(root)
            while True:
                node = nodes[cursor]
                path.append(f"{node.sort}:{node.head}")
                if cursor not in best_child:
                    break
                cursor = best_child[cursor]
            sample = "/".join(path[:12])
            if len(path) > 24:
                sample += "/.../" + "/".join(path[-12:])
            elif len(path) > 12:
                sample += "/" + "/".join(path[12:])
            return depths[id(root)], len(depths), sample

        def traced_normalize(self: Any, tree: Any) -> Any:
            try:
                return original_normalize(self, tree)
            except RecursionError:
                depth, unique_nodes, path = tree_metrics(tree)
                print(
                    "RECURSION_TREE root="
                    f"{tree.sort}:{tree.head} depth={depth} "
                    f"uniqueNodes={unique_nodes} path={path}",
                    file=sys.stderr,
                    flush=True,
                )
                raise

        def traced_emit(self: Any, label: str, available: Any) -> str:
            print(
                "RECURSION_TRACE theorem="
                f"{label} limit={sys.getrecursionlimit()}",
                file=sys.stderr,
                flush=True,
            )
            try:
                return original_emit(self, label, available)
            except RecursionError:
                statement = self.database.statements[label]
                print(
                    "RECURSION_FAILURE theorem="
                    f"{label} proofOps={len(statement.proof_ops)} "
                    f"limit={sys.getrecursionlimit()}",
                    file=sys.stderr,
                    flush=True,
                )
                raise

        emitter_class.emit_theorem = traced_emit
        emitter_class.normalize_recanon = traced_normalize
        return emitter_class

    translator.build_emitter_class = traced_build


def main(argv: Sequence[str] | None = None) -> int:
    diagnostic = argparse.ArgumentParser(add_help=False)
    diagnostic.add_argument(
        "--diagnostic-recursion-limit", type=int, default=200_000
    )
    options, translator_argv = diagnostic.parse_known_args(argv)
    require(options.diagnostic_recursion_limit >= 200_000,
            "diagnostic recursion limit must be at least the v1 limit")
    translator = load_translator()
    install_theorem_trace(translator)
    original_setrecursionlimit = sys.setrecursionlimit
    prior_limit = sys.getrecursionlimit()

    def enforce_floor(requested: int) -> None:
        original_setrecursionlimit(
            max(requested, options.diagnostic_recursion_limit)
        )

    original_setrecursionlimit(options.diagnostic_recursion_limit)
    sys.setrecursionlimit = enforce_floor
    try:
        return int(translator.main(translator_argv))
    finally:
        sys.setrecursionlimit = original_setrecursionlimit
        original_setrecursionlimit(prior_limit)


if __name__ == "__main__":
    raise SystemExit(main())
