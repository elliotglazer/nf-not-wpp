#!/usr/bin/env python3
"""Hash-safe successor to the pinned reusable nominal translator v1.

The v1 translator already raises Python's recursion limit to 200,000.  On
Python 3.12, C-level recursion guards can nevertheless fire near a thousand
nested calls when ``functools.lru_cache`` structurally hashes an ``AST`` at
every recursive definition-expansion boundary.  This successor preserves the
v1 translation byte-for-byte while replacing only those two structural-hash
caches with unbounded identity-key caches.  It is source-only and never starts
Lean.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Callable, Sequence, TypeVar


HERE = Path(__file__).resolve().parent
THIS = Path(__file__).resolve()
PYTHON_SHA256 = "D8E3F0ADF246DB00358C0C4ED349CF714898178F9558FB0E944F79F5C07F8EAA"
PREDECESSOR = HERE / "reusable_nominal_mm_translator_v1.py"
PREDECESSOR_SHA256 = "8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94"
RECURSION_LIMIT = 200_000

T = TypeVar("T")


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


def load_predecessor() -> ModuleType:
    require_hash(Path(sys.executable).resolve(), PYTHON_SHA256,
                 "Python interpreter")
    require_hash(PREDECESSOR, PREDECESSOR_SHA256,
                 "reusable nominal translator v1")
    name = "_reusable_nominal_mm_translator_v1_for_v2"
    require(name not in sys.modules,
            "pinned translator module name was already loaded")
    spec = importlib.util.spec_from_file_location(name, PREDECESSOR)
    require(spec is not None and spec.loader is not None,
            "could not load reusable nominal translator v1")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def install_identity_expander(translator: ModuleType) -> None:
    original_build = translator.build_emitter_class
    installed = False

    def patched_build(backend: Any) -> type:
        nonlocal installed
        choice = backend.wpp_base.choice_replay
        base = choice.ProvenanceBlindExpander
        if not installed:
            expand_wff = getattr(base, "expand_wff", None)
            expand_class = getattr(base, "expand_class", None)
            raw_wff = getattr(expand_wff, "__wrapped__", None)
            raw_class = getattr(expand_class, "__wrapped__", None)
            require(callable(raw_wff) and callable(raw_class),
                    "definition expander is not the pinned lru-cache shape")
            require(getattr(raw_wff, "__name__", None) == "expand_wff"
                    and getattr(raw_class, "__name__", None) == "expand_class",
                    "definition expander wrapped methods changed")

            class IdentityCachedProvenanceBlindExpander(base):
                """V1 expander with hash-free, object-identity memoization."""

                def __init__(self, *args: Any, **kwargs: Any) -> None:
                    super().__init__(*args, **kwargs)
                    self._identity_wff_cache: dict[int, tuple[Any, Any]] = {}
                    self._identity_class_cache: dict[int, tuple[Any, Any]] = {}

                @staticmethod
                def _identity_cached(
                    cache: dict[int, tuple[Any, T]],
                    tree: Any,
                    worker: Callable[[Any], T],
                ) -> T:
                    key = id(tree)
                    prior = cache.get(key)
                    if prior is not None:
                        require(prior[0] is tree,
                                "live AST identity collision in expander cache")
                        return prior[1]
                    result = worker(tree)
                    # Retaining the input object makes reuse of its id
                    # impossible for the lifetime of this unbounded cache.
                    cache[key] = (tree, result)
                    return result

                def expand_wff(self, tree: Any) -> Any:
                    return self._identity_cached(
                        self._identity_wff_cache,
                        tree,
                        lambda value: raw_wff(self, value),
                    )

                def expand_class(self, tree: Any) -> Any:
                    return self._identity_cached(
                        self._identity_class_cache,
                        tree,
                        lambda value: raw_class(self, value),
                    )

            IdentityCachedProvenanceBlindExpander.__name__ = (
                "IdentityCachedProvenanceBlindExpanderV2"
            )
            choice.ProvenanceBlindExpander = (
                IdentityCachedProvenanceBlindExpander
            )
            installed = True
        else:
            require(
                choice.ProvenanceBlindExpander.__name__
                == "IdentityCachedProvenanceBlindExpanderV2",
                "identity expander installation changed during translation",
            )
        return original_build(backend)

    translator.build_emitter_class = patched_build
    # The emitted resource must identify this semantic execution wrapper, not
    # merely the frozen implementation that it delegates to.
    translator.THIS = THIS


def main(argv: Sequence[str] | None = None) -> int:
    translator = load_predecessor()
    install_identity_expander(translator)
    sys.setrecursionlimit(max(sys.getrecursionlimit(), RECURSION_LIMIT))
    return int(translator.main(argv))


if __name__ == "__main__":
    raise SystemExit(main())
