#!/usr/bin/env python3
"""Manifest-driven WPP FV dispatch with direct-first DV certificates.

The inherited Choice fallback tried structural ``simp``/``aesop`` before an
already available source-DV hypothesis.  In a large WPP context that made an
exact source hypothesis needlessly expand to a quantified disjointness goal
and exhaust aesop's rule budget.  This append-only revision makes ``assumption``
the first fallback branch and emits a named source fact directly for atomic
non-setvar DV pairs in their source orientation.
"""

from __future__ import annotations

import emit_wpp_compact_replay_fv_dispatch as v1


choice_replay = v1.choice_replay
json_bytes = v1.json_bytes
INTRA_THEOREM_LIFT_PROOF_OPS = v1.INTRA_THEOREM_LIFT_PROOF_OPS


class WPPCompactEmitterFVDispatchDirectDV(v1.WPPCompactEmitterFVDispatch):
    def dv_tactic(self, *trees):  # type: ignore[no-untyped-def]
        lemmas: list[str] = []
        seen: set[str] = set()
        for tree in trees:
            for lemma in self.fv_lemmas(tree):
                if lemma not in seen:
                    seen.add(lemma)
                    lemmas.append(lemma)
        lemmas.extend(
            [
                "Finset.mem_union",
                "Finset.mem_erase",
                "Finset.mem_singleton",
                "Finset.disjoint_left",
            ]
        )
        simp_set = ", ".join(lemmas)
        tactic = (
            "(by first | assumption | "
            "(simp (config := { failIfUnchanged := false }) "
            f"only [{simp_set}] at ⊢ <;> aesop))"
        )

        if len(trees) == 2:
            left, right = trees
            if (
                left.is_variable
                and right.is_variable
                and left.sort in {"wff", "class"}
                and right.sort in {"wff", "class"}
            ):
                source = self._source_dv_fact(
                    left.variable_name, right.variable_name
                )
                if source is not None and source[1] is False:
                    target = self.substituted_dv_type(left, right)
                    tactic = f"(show {target} from (by exact {source[0]}))"

        if self._dv_cache is not None and len(trees) == 2:
            structural = self.structural_dv_tactic(trees[0], trees[1])
            if structural is not None:
                tactic = structural
        if self._dv_cache is None:
            return tactic
        if len(trees) != 2:
            raise v1.base.MMError(f"cached DV expected two trees, got {len(trees)}")
        target = self.substituted_dv_type(trees[0], trees[1])
        cached = self._dv_cache.get(target)
        if cached is None:
            name = f"dv_cache_{len(self._dv_cache) + 1:04d}"
            self._dv_cache[target] = (name, tactic)
        else:
            name = cached[0]
        return name


def load_frontend(leaf_manifests):  # type: ignore[no-untyped-def]
    # The v1 loader resolves this class through its module global at call time.
    # Patch it only for this construction, then restore it before returning.
    previous = v1.WPPCompactEmitterFVDispatch
    v1.WPPCompactEmitterFVDispatch = WPPCompactEmitterFVDispatchDirectDV
    try:
        return v1.load_frontend(leaf_manifests)
    finally:
        v1.WPPCompactEmitterFVDispatch = previous

