#!/usr/bin/env python3
"""Structural Disjoint certificates aligned with Lean's union associativity.

The v3 structural emitter decomposed an n-ary FV union from the leftmost atom
into a right-nested proof.  The emitted FV expression uses infix ``∪``, which
Lean parses left-associatively.  This append-only revision folds certificates
in the same left-associated order as the printed expression.
"""

from __future__ import annotations

import emit_wpp_compact_replay_fv_dispatch_v3 as v3


choice_replay = v3.choice_replay
json_bytes = v3.json_bytes
INTRA_THEOREM_LIFT_PROOF_OPS = v3.INTRA_THEOREM_LIFT_PROOF_OPS
base = v3.base


class WPPCompactEmitterStructuralDisjointAssoc(
    v3.WPPCompactEmitterStructuralDisjoint
):
    def _disjoint_support_term(self, left: tuple, right: tuple) -> str:
        left_expr = self._fv_support_expr(left)
        right_expr = self._fv_support_expr(right)
        target = f"Disjoint ({left_expr}) ({right_expr})"

        if left[0] == "union":
            items = left[1]
            if not items:
                return f"(show {target} from (by simp))"
            result = self._disjoint_support_term(items[0], right)
            for item in items[1:]:
                next_proof = self._disjoint_support_term(item, right)
                result = (
                    "(Finset.disjoint_union_left.mpr "
                    f"⟨{result}, {next_proof}⟩)"
                )
            return f"(show {target} from {result})"

        if right[0] == "union":
            items = right[1]
            if not items:
                return f"(show {target} from (by simp))"
            result = self._disjoint_support_term(left, items[0])
            for item in items[1:]:
                next_proof = self._disjoint_support_term(left, item)
                result = (
                    "(Finset.disjoint_union_right.mpr "
                    f"⟨{result}, {next_proof}⟩)"
                )
            return f"(show {target} from {result})"

        return super()._disjoint_support_term(left, right)


def load_frontend(leaf_manifests):  # type: ignore[no-untyped-def]
    previous = v3.v2.v1.WPPCompactEmitterFVDispatch
    v3.v2.v1.WPPCompactEmitterFVDispatch = (
        WPPCompactEmitterStructuralDisjointAssoc
    )
    try:
        return v3.v2.v1.load_frontend(leaf_manifests)
    finally:
        v3.v2.v1.WPPCompactEmitterFVDispatch = previous

