#!/usr/bin/env python3
"""Manifest FV dispatch with recursive, search-free Disjoint certificates."""

from __future__ import annotations

import emit_wpp_compact_replay_fv_dispatch_v2 as v2


choice_replay = v2.choice_replay
json_bytes = v2.json_bytes
INTRA_THEOREM_LIFT_PROOF_OPS = v2.INTRA_THEOREM_LIFT_PROOF_OPS
base = v2.v1.base


class WPPCompactEmitterStructuralDisjoint(v2.WPPCompactEmitterFVDispatchDirectDV):
    def _atomic_disjoint_term(self, left: base.AST, right: base.AST) -> str:
        if not (
            left.is_variable and right.is_variable
            and left.sort in {"wff", "class"}
            and right.sort in {"wff", "class"}
        ):
            raise base.MMError("non-atomic support in atomic Disjoint certificate")
        target = self.substituted_dv_type(left, right)
        left_name = choice_replay.safe(left.variable_name)
        right_name = choice_replay.safe(right.variable_name)
        if left.variable_name in self._current_local_sorts:
            return (
                f"(show {target} from "
                f"(by simp [{left_name}, Wff.fv, Class.fv]))"
            )
        if right.variable_name in self._current_local_sorts:
            return (
                f"(show {target} from "
                f"(by simp [{right_name}, Wff.fv, Class.fv]))"
            )
        source = self._source_dv_fact(left.variable_name, right.variable_name)
        if source is None:
            return f"(show {target} from (by assumption))"
        fact, reverse = source
        proof = f"{fact}.symm" if reverse else fact
        return f"(show {target} from (by exact {proof}))"

    def _disjoint_support_term(self, left: tuple, right: tuple) -> str:
        left_expr = self._fv_support_expr(left)
        right_expr = self._fv_support_expr(right)
        target = f"Disjoint ({left_expr}) ({right_expr})"
        left_tag = left[0]
        right_tag = right[0]

        if left_tag == "empty" or right_tag == "empty":
            return f"(show {target} from (by simp))"
        if left_tag == "tree":
            tree = left[1]
            if tree.is_variable:
                if right_tag == "tree" and right[1].is_variable:
                    return self._atomic_disjoint_term(tree, right[1])
            else:
                lemma, support = self._head_fv_support(tree)
                inner = self._disjoint_support_term(support, right)
                return f"(show {target} from (by rw [{lemma}]; exact {inner}))"
        if right_tag == "tree" and not right[1].is_variable:
            lemma, support = self._head_fv_support(right[1])
            inner = self._disjoint_support_term(left, support)
            return f"(show {target} from (by rw [{lemma}]; exact {inner}))"

        if left_tag == "union":
            items = left[1]
            if not items:
                return f"(show {target} from (by simp))"
            result = self._disjoint_support_term(items[-1], right)
            for item in reversed(items[:-1]):
                first = self._disjoint_support_term(item, right)
                result = (
                    "(Finset.disjoint_union_left.mpr "
                    f"⟨{first}, {result}⟩)"
                )
            return f"(show {target} from {result})"
        if right_tag == "union":
            items = right[1]
            if not items:
                return f"(show {target} from (by simp))"
            result = self._disjoint_support_term(left, items[-1])
            for item in reversed(items[:-1]):
                first = self._disjoint_support_term(left, item)
                result = (
                    "(Finset.disjoint_union_right.mpr "
                    f"⟨{first}, {result}⟩)"
                )
            return f"(show {target} from {result})"

        if left_tag == "erase_tree":
            inner = self._disjoint_support_term(left[1], right)
            subset = f"(Finset.erase_subset {self.qualified_expr(left[2])} _)"
            return (
                f"(show {target} from "
                f"(Disjoint.mono_left {subset} {inner}))"
            )
        if right_tag == "erase_tree":
            inner = self._disjoint_support_term(left, right[1])
            subset = f"(Finset.erase_subset {self.qualified_expr(right[2])} _)"
            return (
                f"(show {target} from "
                f"(Disjoint.mono_right {subset} {inner}))"
            )

        if left_tag == "singleton_tree":
            not_mem = self._not_mem_support_term(left[1], right)
            return (
                f"(show {target} from "
                f"(Finset.disjoint_singleton_left.mpr {not_mem}))"
            )
        if right_tag == "singleton_tree":
            not_mem = self._not_mem_support_term(right[1], left)
            return (
                f"(show {target} from "
                f"(Finset.disjoint_singleton_right.mpr {not_mem}))"
            )

        if left_tag == "pair_tree":
            left_not = self._not_mem_support_term(left[1], right)
            right_not = self._not_mem_support_term(left[2], right)
            proof = (
                "(Finset.disjoint_left.mpr (by intro a ha hb; "
                "simp only [Finset.mem_insert, Finset.mem_singleton] at ha; "
                "rcases ha with rfl | rfl; "
                f"exact {left_not} hb; exact {right_not} hb))"
            )
            return f"(show {target} from {proof})"
        if right_tag == "pair_tree":
            left_not = self._not_mem_support_term(right[1], left)
            right_not = self._not_mem_support_term(right[2], left)
            proof = (
                "(Finset.disjoint_left.mpr (by intro a ha hb; "
                "simp only [Finset.mem_insert, Finset.mem_singleton] at hb; "
                "rcases hb with rfl | rfl; "
                f"exact {left_not} ha; exact {right_not} ha))"
            )
            return f"(show {target} from {proof})"

        # A tree/tree pair reaches here only when at least one atom is a
        # non-variable proof-local support.  Keep the fallback deterministic.
        if left_tag == "tree" and right_tag == "tree":
            return self._atomic_disjoint_term(left[1], right[1])
        raise base.MMError(
            f"unsupported structural Disjoint support: {left_tag}/{right_tag}"
        )

    def structural_dv_tactic(self, left: base.AST, right: base.AST) -> str | None:
        inherited = super().structural_dv_tactic(left, right)
        if inherited is not None:
            return inherited
        if left.sort not in {"wff", "class"} or right.sort not in {"wff", "class"}:
            return None
        left_support = (
            ("tree", left) if left.is_variable else self._head_fv_support(left)[1]
        )
        right_support = (
            ("tree", right) if right.is_variable else self._head_fv_support(right)[1]
        )
        target = self.substituted_dv_type(left, right)
        proof = self._disjoint_support_term(left_support, right_support)
        left_lemma = None if left.is_variable else self._head_fv_support(left)[0]
        right_lemma = None if right.is_variable else self._head_fv_support(right)[0]
        rewrites = [lemma for lemma in (left_lemma, right_lemma) if lemma]
        if rewrites:
            return (
                f"(show {target} from "
                f"(by rw [{', '.join(rewrites)}]; exact {proof}))"
            )
        return f"(show {target} from {proof})"


def load_frontend(leaf_manifests):  # type: ignore[no-untyped-def]
    previous = v2.v1.WPPCompactEmitterFVDispatch
    v2.v1.WPPCompactEmitterFVDispatch = WPPCompactEmitterStructuralDisjoint
    try:
        return v2.v1.load_frontend(leaf_manifests)
    finally:
        v2.v1.WPPCompactEmitterFVDispatch = previous

