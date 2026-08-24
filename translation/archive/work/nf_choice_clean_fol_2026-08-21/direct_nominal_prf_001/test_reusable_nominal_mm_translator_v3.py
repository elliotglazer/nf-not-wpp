#!/usr/bin/env python3
"""Source-only regression checks for reusable_nominal_mm_translator_v3."""

from __future__ import annotations

import importlib.util
from pathlib import Path
from types import SimpleNamespace
import sys
import unittest


HERE = Path(__file__).resolve().parent
TRANSLATOR = HERE / "reusable_nominal_mm_translator_v3.py"


def load_v3():  # type: ignore[no-untyped-def]
    name = "_reusable_nominal_mm_translator_v3_regression"
    spec = importlib.util.spec_from_file_location(name, TRANSLATOR)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load reusable nominal translator v3")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class TranslatorV3Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.v3 = load_v3()
        v2 = cls.v3.load_predecessor()
        v1 = v2.load_predecessor()
        v2.install_identity_expander(v1)
        cls.v3.install_exact_fv_rewrite_dedup(v1)
        backend = v1.load_backend("WPP_PROFILE_V2")
        cls.v3_emitter = v1.build_emitter_class(backend)
        cls.v2_emitter = cls.v3_emitter.__mro__[1]

    @staticmethod
    def harness(emitter):  # type: ignore[no-untyped-def]
        class Harness(emitter):
            def _head_fv_support(self, tree):  # type: ignore[no-untyped-def]
                return tree.lemma, tree.support

            def _applied_head_fv_lemma(
                self, tree, lemma,  # type: ignore[no-untyped-def]
            ):
                if tree.lemma != lemma:
                    raise AssertionError("test lemma changed")
                return tree.applied

            def substituted_dv_type(
                self, left, right,  # type: ignore[no-untyped-def]
            ):
                return "TARGET"

            def _disjoint_support_term(
                self, left, right,  # type: ignore[no-untyped-def]
            ):
                return "PROOF"

        return object.__new__(Harness)

    @staticmethod
    def tree(applied: str):
        return SimpleNamespace(
            sort="class",
            is_variable=False,
            lemma="fv_root",
            support=("empty",),
            applied=applied,
        )

    def test_identical_applied_rewrite_is_emitted_once(self) -> None:
        left = self.tree("fv_syn_cvv")
        right = self.tree("fv_syn_cvv")
        old = self.harness(self.v2_emitter).structural_dv_tactic(
            left, right
        )
        new = self.harness(self.v3_emitter).structural_dv_tactic(
            left, right
        )
        self.assertEqual(
            old,
            "(show TARGET from "
            "(by rw [fv_syn_cvv, fv_syn_cvv]; exact PROOF))",
        )
        self.assertEqual(
            new,
            "(show TARGET from (by rw [fv_syn_cvv]; exact PROOF))",
        )

    def test_same_lemma_with_different_arguments_is_byte_unchanged(self) -> None:
        left = self.tree("fv_pair (LEFT)")
        right = self.tree("fv_pair (RIGHT)")
        old = self.harness(self.v2_emitter).structural_dv_tactic(
            left, right
        )
        new = self.harness(self.v3_emitter).structural_dv_tactic(
            left, right
        )
        self.assertEqual(new, old)
        self.assertEqual(
            new,
            "(show TARGET from "
            "(by rw [fv_pair (LEFT), fv_pair (RIGHT)]; exact PROOF))",
        )


if __name__ == "__main__":
    unittest.main()
