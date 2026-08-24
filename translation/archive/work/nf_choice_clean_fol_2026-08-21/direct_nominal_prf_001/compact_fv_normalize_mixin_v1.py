#!/usr/bin/env python3
"""Alpha-neutral compact FV-certificate mixin.

This module deliberately imports no Metamath parser, nominal emitter, alpha
frontier, WPP endpoint, or generated resource.  A host emitter supplies the
small structural-FV protocol listed in ``REQUIRED_HOST_METHODS`` and may set
``compact_fv_error_type`` to its checked parser error class.  The mixin then
replaces only setvar/nonset DV certificates with one deterministic ``simp
only`` normalization over audited FV equations and exact atomic facts.

Every unsupported syntax shape or absent leaf fact fails closed.  Setvar
inequalities and nonset/nonset Disjoint obligations are delegated through the
MRO to the host's existing structural implementation.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import re


THIS = Path(__file__).resolve()
REQUIRED_HOST_METHODS = (
    "fv_lemmas",
    "_head_fv_support",
    "_source_dv_fact",
    "qualified_expr",
    "structural_dv_tactic",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def safe(name: str) -> str:
    result = re.sub(r"[^A-Za-z0-9_]", "_", name)
    return "n_" + result if not result or result[0].isdigit() else result


class CompactFVNormalizeMixin:
    """Backend-neutral structural_dv_tactic override."""

    compact_fv_error_type: type[Exception] = RuntimeError

    _FINSET_NORMALIZERS = (
        "Finset.mem_union",
        "Finset.mem_erase",
        "Finset.mem_insert",
        "Finset.mem_singleton",
    )
    _BOOL_NORMALIZERS = (
        "false_or",
        "or_false",
        "true_and",
        "and_true",
        "false_and",
        "and_false",
        "not_false_eq_true",
    )

    def _compact_fv_fail(self, message: str):  # type: ignore[no-untyped-def]
        raise self.compact_fv_error_type(message)

    @staticmethod
    def _append_unique(items: list[str], seen: set[str], item: str) -> None:
        if item not in seen:
            seen.add(item)
            items.append(item)

    def _inequality_fact(self, left, right):  # type: ignore[no-untyped-def]
        if not (
            left.is_variable
            and right.is_variable
            and left.sort == "setvar"
            and right.sort == "setvar"
        ):
            self._compact_fv_fail(
                "compact FV singleton contains a non-setvar atom"
            )
        if left.variable_name == right.variable_name:
            self._compact_fv_fail(
                "compact FV certificate requested strict self-DV"
            )
        left_name = safe(left.variable_name)
        right_name = safe(right.variable_name)
        if (
            left.variable_name in self._current_local_sorts
            or right.variable_name in self._current_local_sorts
        ):
            return f"fresh_{left_name}_ne_{right_name}"
        source = self._source_dv_fact(left.variable_name, right.variable_name)
        if source is None:
            self._compact_fv_fail(
                "missing atomic source DV in compact FV certificate: "
                f"{left.variable_name}/{right.variable_name}"
            )
        fact, reverse = source
        return f"(Ne.symm {fact})" if reverse else fact

    def _atomic_not_mem_fact(self, variable, tree):  # type: ignore[no-untyped-def]
        if not (
            variable.is_variable
            and variable.sort == "setvar"
            and tree.is_variable
            and tree.sort in {"wff", "class"}
        ):
            self._compact_fv_fail(
                "bad atom in compact FV nonmembership certificate"
            )
        variable_name = safe(variable.variable_name)
        tree_name = safe(tree.variable_name)
        if tree.variable_name in self._current_local_sorts:
            return (tree_name, "Wff.fv", "Class.fv")
        if variable.variable_name in self._current_local_sorts:
            return (f"fresh_{variable_name}_not_{tree_name}",)
        source = self._source_dv_fact(variable.variable_name, tree.variable_name)
        if source is None:
            self._compact_fv_fail(
                "missing atomic source FV fact in compact certificate: "
                f"{variable.variable_name}/{tree.variable_name}"
            )
        return (source[0],)

    def _collect_support_facts(
        self,
        variable,
        support: tuple,
        items: list[str],
        seen: set[str],
    ) -> None:  # type: ignore[no-untyped-def]
        tag = support[0]
        if tag == "empty":
            return
        if tag == "tree":
            tree = support[1]
            if tree.is_variable:
                for fact in self._atomic_not_mem_fact(variable, tree):
                    self._append_unique(items, seen, fact)
                return
            _lemma, nested = self._head_fv_support(tree)
            self._collect_support_facts(variable, nested, items, seen)
            return
        if tag == "singleton_tree":
            self._append_unique(
                items, seen, self._inequality_fact(variable, support[1])
            )
            return
        if tag == "pair_tree":
            self._append_unique(
                items, seen, self._inequality_fact(variable, support[1])
            )
            self._append_unique(
                items, seen, self._inequality_fact(variable, support[2])
            )
            return
        if tag == "union":
            for nested in support[1]:
                self._collect_support_facts(variable, nested, items, seen)
            return
        if tag == "erase_tree":
            if variable != support[2]:
                self._collect_support_facts(
                    variable, support[1], items, seen
                )
            return
        self._compact_fv_fail(f"unsupported compact FV support tag: {tag}")

    def _compact_not_mem_tactic(self, variable, tree):  # type: ignore[no-untyped-def]
        if not (
            variable.is_variable
            and variable.sort == "setvar"
            and tree.sort in {"wff", "class"}
        ):
            self._compact_fv_fail(
                "compact FV normalization received bad sorts"
            )

        items: list[str] = []
        seen: set[str] = set()
        for lemma in self.fv_lemmas(tree):
            self._append_unique(items, seen, lemma)
        for lemma in self._FINSET_NORMALIZERS:
            self._append_unique(items, seen, lemma)

        if tree.is_variable:
            for fact in self._atomic_not_mem_fact(variable, tree):
                self._append_unique(items, seen, fact)
        else:
            _root_lemma, support = self._head_fv_support(tree)
            self._collect_support_facts(variable, support, items, seen)

        empty_fact = "compact_fv_not_mem_empty"
        self._append_unique(items, seen, empty_fact)
        for lemma in self._BOOL_NORMALIZERS:
            self._append_unique(items, seen, lemma)
        simp_set = ", ".join(items)
        variable_expr = self.qualified_expr(variable)
        return (
            "(by\n"
            f"      have {empty_fact} : {variable_expr} ∉ "
            "(∅ : Finset Var) := by\n"
            "        intro hmem\n"
            "        cases hmem\n"
            f"      simp only [{simp_set}])"
        )

    def structural_dv_tactic(self, left, right):  # type: ignore[no-untyped-def]
        if left.sort == "setvar" and right.sort in {"wff", "class"}:
            return self._compact_not_mem_tactic(left, right)
        if right.sort == "setvar" and left.sort in {"wff", "class"}:
            return self._compact_not_mem_tactic(right, left)
        return super().structural_dv_tactic(left, right)


def verify_host_class(host: type) -> None:
    missing = [name for name in REQUIRED_HOST_METHODS if not hasattr(host, name)]
    if missing:
        raise RuntimeError(
            "compact FV host lacks structural protocol methods: "
            + ", ".join(missing)
        )


def provenance() -> dict[str, object]:
    return {
        "schema": "nf-compact-fv-normalize-mixin-v1",
        "module": str(THIS),
        "moduleSha256": sha256(THIS),
        "alphaNeutral": True,
        "requiredHostMethods": REQUIRED_HOST_METHODS,
        "normalizedCase": "setvar/nonset FV nonmembership",
        "atomicLeafPolicy": "exact source/local facts; fail closed if absent",
        "emptySupportPolicy": "explicit local cases certificate",
        "tacticPolicy": "single deterministic simp only; no search/fallback",
        "delegatedCases": (
            "setvar/setvar inequality",
            "nonset/nonset structural Disjoint",
        ),
    }

