#!/usr/bin/env python3
"""Hash-safe successor fixing duplicate nullary FV rewrites.

The pinned v2 translator is retained in full, including its identity-key
definition-expansion caches.  This successor changes one emitter corner case:
when the two structural distinct-variable operands produce the *same exact*
applied root-FV rewrite, it emits that rewrite once.  Lean's ``rw`` rewrites
all matching occurrences, so repeating an identical nullary theorem leaves no
second occurrence and fails.  Applied rewrites that differ (including the same
lemma at different constructor arguments) continue through the v2 emitter
unchanged.

This translator is source-only and never starts Lean.
"""

from __future__ import annotations

import hashlib
import importlib.util
import inspect
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Sequence


HERE = Path(__file__).resolve().parent
THIS = Path(__file__).resolve()
PYTHON_SHA256 = "D8E3F0ADF246DB00358C0C4ED349CF714898178F9558FB0E944F79F5C07F8EAA"
PREDECESSOR = HERE / "reusable_nominal_mm_translator_v2.py"
PREDECESSOR_SHA256 = "52ED85A33329D1D4CE0E9D05622F74917E1CD9662959AAD7D7B6175244F34615"
HOST_METHOD_SOURCE_SHA256 = (
    "F1362A81A8F6C404DCC7199E10285AD31DD8EDA457651B274AA44D31E4691E45"
)
RECURSION_LIMIT = 200_000


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


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
                 "reusable nominal translator v2")
    name = "_reusable_nominal_mm_translator_v2_for_v3"
    require(name not in sys.modules,
            "pinned translator v2 module name was already loaded")
    spec = importlib.util.spec_from_file_location(name, PREDECESSOR)
    require(spec is not None and spec.loader is not None,
            "could not load reusable nominal translator v2")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def install_exact_fv_rewrite_dedup(translator: ModuleType) -> None:
    """Wrap only the exact-identical repeated-root-FV corner case."""

    original_build = translator.build_emitter_class

    def patched_build(backend: Any) -> type:
        host = backend.structural.WPPCompactEmitterExactRepeatedRootFV
        method = host.__dict__.get("structural_dv_tactic")
        require(host.__name__ == "WPPCompactEmitterExactRepeatedRootFV",
                "structural FV host class changed")
        require(host.__module__ == "emit_wpp_compact_replay_fv_dispatch_v5",
                "structural FV host module changed")
        require(callable(method), "structural FV host method is not direct")
        method_source = inspect.getsource(method).encode("utf-8")
        require(
            sha256_bytes(method_source) == HOST_METHOD_SOURCE_SHA256,
            "structural FV host method source changed",
        )

        base_emitter = original_build(backend)

        class ExactFVRewriteDedupEmitterV3(base_emitter):
            """V2 emitter with exact duplicate root-FV rewrites collapsed."""

            def structural_dv_tactic(
                self, left: Any, right: Any,
            ) -> str | None:
                if (
                    left.sort in {"wff", "class"}
                    and right.sort in {"wff", "class"}
                    and not left.is_variable
                    and not right.is_variable
                ):
                    left_lemma, left_support = self._head_fv_support(left)
                    right_lemma, right_support = self._head_fv_support(right)
                    if left_lemma == right_lemma:
                        exact_left = self._applied_head_fv_lemma(
                            left, left_lemma
                        )
                        exact_right = self._applied_head_fv_lemma(
                            right, right_lemma
                        )
                        if exact_left == exact_right:
                            target = self.substituted_dv_type(left, right)
                            proof = self._disjoint_support_term(
                                left_support, right_support
                            )
                            return (
                                f"(show {target} from "
                                f"(by rw [{exact_left}]; exact {proof}))"
                            )
                # Every non-identical case, including equal lemma names with
                # different applied arguments, is emitted by pinned v2 code.
                return super().structural_dv_tactic(left, right)

        ExactFVRewriteDedupEmitterV3.__name__ = (
            "ExactFVRewriteDedupEmitterV3"
        )
        return ExactFVRewriteDedupEmitterV3

    translator.build_emitter_class = patched_build
    # The emitted resource identifies this semantic successor.
    translator.THIS = THIS


def main(argv: Sequence[str] | None = None) -> int:
    predecessor = load_predecessor()
    translator = predecessor.load_predecessor()
    predecessor.install_identity_expander(translator)
    install_exact_fv_rewrite_dedup(translator)
    sys.setrecursionlimit(max(sys.getrecursionlimit(), RECURSION_LIMIT))
    return int(translator.main(argv))


if __name__ == "__main__":
    raise SystemExit(main())
