#!/usr/bin/env python3
"""Exact repeated-root FV rewrites for structural Disjoint certificates.

When both sides have the same non-atomic head, an unqualified ``rw [h, h]``
rewrites the leftmost nested occurrence twice.  Apply each FV theorem to the
exact constructor arguments so the first rewrite targets the left root and the
second targets the right root.
"""

from __future__ import annotations

import emit_wpp_compact_replay_fv_dispatch_v4 as v4


choice_replay = v4.choice_replay
json_bytes = v4.json_bytes
INTRA_THEOREM_LIFT_PROOF_OPS = v4.INTRA_THEOREM_LIFT_PROOF_OPS
base = v4.base


class WPPCompactEmitterExactRepeatedRootFV(
    v4.WPPCompactEmitterStructuralDisjointAssoc
):
    def _applied_head_fv_lemma(self, tree: base.AST, lemma: str) -> str:
        arguments = " ".join(
            f"({self.qualified_expr(argument)})" for argument in tree.args
        )
        return f"{lemma} {arguments}" if arguments else lemma

    def structural_dv_tactic(self, left: base.AST, right: base.AST) -> str | None:
        if (
            left.sort in {"wff", "class"}
            and right.sort in {"wff", "class"}
            and not left.is_variable
            and not right.is_variable
        ):
            left_lemma, left_support = self._head_fv_support(left)
            right_lemma, right_support = self._head_fv_support(right)
            if left_lemma == right_lemma:
                target = self.substituted_dv_type(left, right)
                proof = self._disjoint_support_term(left_support, right_support)
                exact_left = self._applied_head_fv_lemma(left, left_lemma)
                exact_right = self._applied_head_fv_lemma(right, right_lemma)
                return (
                    f"(show {target} from "
                    f"(by rw [{exact_left}, {exact_right}]; exact {proof}))"
                )
        return super().structural_dv_tactic(left, right)


def load_frontend(leaf_manifests):  # type: ignore[no-untyped-def]
    previous = v4.v3.v2.v1.WPPCompactEmitterFVDispatch
    v4.v3.v2.v1.WPPCompactEmitterFVDispatch = (
        WPPCompactEmitterExactRepeatedRootFV
    )
    try:
        return v4.v3.v2.v1.load_frontend(leaf_manifests)
    finally:
        v4.v3.v2.v1.WPPCompactEmitterFVDispatch = previous
