#!/usr/bin/env python3
"""Oriented expansion of the 140 ``df-*`` leaves in the nchoice closure.

Class constructor definitions are equations and ordinary wff constructor
definitions are biconditionals.  The two exceptional propositional constants
(``df-bi`` and ``df-tru``) are given their primitive expansions explicitly.
The overloaded class primitives ``wceq``/``wcel`` and class abstraction
``cab`` are intentionally retained for the semantic backend; their three
source definitions become checked semantic lemmas rather than textual rewrite
rules.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
import hashlib
from typing import Iterable, Mapping

from ast_replay import ASTReplayer, instantiate
from mm_parser import Database, MMError, Statement
from syntax import AST


SEMANTIC_DEFINITIONS = frozenset({"df-clab", "df-cleq", "df-clel"})
LOGICAL_CORE = frozenset({"wn", "wi", "wal", "weq", "wel", "wceq", "wcel"})
CLASS_CORE = frozenset({"cv", "cab"})


def variables(tree: AST) -> frozenset[tuple[str, str]]:
    if tree.is_variable:
        return frozenset({(tree.sort, tree.variable_name)})
    result: set[tuple[str, str]] = set()
    for argument in tree.args:
        result.update(variables(argument))
    return frozenset(result)


@lru_cache(maxsize=None)
def ast_digest(tree: AST) -> str:
    """Stable structural digest without expanding shared subtrees to text."""

    digest = hashlib.sha256()
    digest.update(tree.sort.encode("utf-8"))
    digest.update(b"\0")
    digest.update(tree.head.encode("utf-8"))
    for argument in tree.args:
        digest.update(b"\0")
        digest.update(bytes.fromhex(ast_digest(argument)))
    return digest.hexdigest()


@dataclass(frozen=True, slots=True)
class DefinitionRule:
    label: str
    target_head: str
    target_sort: str
    lhs: AST
    rhs: AST
    dummy_variables: tuple[tuple[str, str], ...]
    ordinal: int

    def to_data(self) -> object:
        return {
            "label": self.label,
            "target_head": self.target_head,
            "target_sort": self.target_sort,
            "lhs": self.lhs.to_data(),
            "rhs": self.rhs.to_data(),
            "dummy_variables": [
                {"sort": sort, "name": name}
                for sort, name in self.dummy_variables
            ],
            "ordinal": self.ordinal,
        }


def _special_biconditional_rule(statement: Statement) -> DefinitionRule:
    ph = AST.variable("wff", "ph")
    ps = AST.variable("wff", "ps")
    lhs = AST("wff", "wb", (ph, ps))
    # -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
    rhs = AST(
        "wff",
        "wn",
        (
            AST(
                "wff",
                "wi",
                (
                    AST("wff", "wi", (ph, ps)),
                    AST("wff", "wn", (AST("wff", "wi", (ps, ph)),)),
                ),
            ),
        ),
    )
    return DefinitionRule(
        statement.label,
        "wb",
        "wff",
        lhs,
        rhs,
        (),
        statement.ordinal,
    )


def extract_rules(
    database: Database, replayer: ASTReplayer, endpoint: str = "nchoice"
) -> tuple[DefinitionRule, ...]:
    """Extract every safe syntactic rewrite rule in source order."""

    result: list[DefinitionRule] = []
    seen_heads: set[tuple[str, str]] = set()
    for statement in database.dependency_closure(endpoint):
        if statement.kind != "$a" or not statement.label.startswith("df-"):
            continue
        if statement.label in SEMANTIC_DEFINITIONS or statement.label == "df-tru":
            continue
        if statement.label == "df-bi":
            rule = _special_biconditional_rule(statement)
        else:
            schema = replayer.schema[statement.label]
            if schema.head not in {"wb", "wceq"} or len(schema.args) != 2:
                raise MMError(
                    f"cannot orient definition {statement.label}: {schema.sexpr()}"
                )
            lhs, rhs = schema.args
            if schema.head == "wb" and lhs.sort != "wff":
                raise MMError(f"non-wff biconditional lhs at {statement.label}")
            if schema.head == "wceq" and lhs.sort != "class":
                raise MMError(f"non-class equality lhs at {statement.label}")
            if lhs.is_variable:
                raise MMError(f"definition {statement.label} has variable lhs")
            dummies = tuple(sorted(variables(rhs) - variables(lhs)))
            rule = DefinitionRule(
                statement.label,
                lhs.head,
                lhs.sort,
                lhs,
                rhs,
                dummies,
                statement.ordinal,
            )
        key = (rule.target_sort, rule.target_head)
        if key in seen_heads:
            raise MMError(f"multiple syntactic definitions for {key}")
        seen_heads.add(key)
        result.append(rule)
    return tuple(result)


def _match(pattern: AST, actual: AST, bindings: dict[str, AST]) -> bool:
    if pattern.sort != actual.sort:
        return False
    if pattern.is_variable:
        name = pattern.variable_name
        old = bindings.get(name)
        if old is None:
            bindings[name] = actual
            return True
        return old == actual
    if pattern.head != actual.head or len(pattern.args) != len(actual.args):
        return False
    return all(
        _match(pattern_arg, actual_arg, bindings)
        for pattern_arg, actual_arg in zip(pattern.args, actual.args)
    )


class Expander:
    """Deterministic, capture-safe normalizer to the semantic core."""

    def __init__(self, rules: Iterable[DefinitionRule]) -> None:
        self.rules = tuple(rules)
        self.by_head = {
            (rule.target_sort, rule.target_head): rule for rule in self.rules
        }
        self.applied_labels: set[str] = set()

    @staticmethod
    def _fresh_dummy(rule: DefinitionRule, sort: str, name: str, actual: AST) -> AST:
        digest = ast_digest(actual)[:16]
        clean_label = rule.label.replace("-", "_")
        return AST.variable(sort, f"__{clean_label}_{name}_{digest}")

    def _apply(self, rule: DefinitionRule, actual: AST) -> AST:
        bindings: dict[str, AST] = {}
        if not _match(rule.lhs, actual, bindings):
            raise MMError(
                f"definition pattern mismatch for {rule.label}: {actual.sexpr()}"
            )
        for sort, name in rule.dummy_variables:
            if sort == "wff":
                raise MMError(
                    f"unresolved dummy wff in {rule.label}; use an explicit special rule"
                )
            bindings[name] = self._fresh_dummy(rule, sort, name, actual)
        self.applied_labels.add(rule.label)
        return instantiate(rule.rhs, bindings)

    @lru_cache(maxsize=None)
    def expand_class(self, tree: AST) -> AST:
        if tree.sort != "class":
            raise MMError(f"expected class AST, got {tree.sort}")
        if tree.is_variable:
            return tree
        if tree.head == "cv":
            return AST("class", "cv", tree.args)
        if tree.head == "cab":
            if len(tree.args) != 2:
                raise MMError(f"malformed cab: {tree.sexpr()}")
            return AST(
                "class",
                "cab",
                (tree.args[0], self.expand_wff(tree.args[1])),
            )
        rule = self.by_head.get(("class", tree.head))
        if rule is None:
            raise MMError(f"no class definition for {tree.head}")
        return self.expand_class(self._apply(rule, tree))

    @lru_cache(maxsize=None)
    def expand_wff(self, tree: AST) -> AST:
        if tree.sort != "wff":
            raise MMError(f"expected wff AST, got {tree.sort}")
        if tree.is_variable:
            return tree
        if tree.head in {"weq", "wel"}:
            return AST(
                "wff",
                tree.head,
                tuple(tree.args),
            )
        if tree.head in {"wceq", "wcel"}:
            return AST(
                "wff",
                tree.head,
                tuple(self.expand_class(argument) for argument in tree.args),
            )
        if tree.head == "wn":
            return AST("wff", "wn", (self.expand_wff(tree.args[0]),))
        if tree.head == "wi":
            return AST(
                "wff", "wi", tuple(self.expand_wff(arg) for arg in tree.args)
            )
        if tree.head == "wal":
            return AST(
                "wff", "wal", (tree.args[0], self.expand_wff(tree.args[1]))
            )
        if tree.head == "wbot":
            return tree
        if tree.head == "wtru":
            # df-tru permits any tautology.  This closed choice is deterministic
            # and avoids carrying its dummy wff metavariable into the core.
            self.applied_labels.add("df-tru")
            tautology_seed = AST("wff", "wbot")
            return AST("wff", "wi", (tautology_seed, tautology_seed))
        rule = self.by_head.get(("wff", tree.head))
        if rule is None:
            raise MMError(f"no wff definition for {tree.head}")
        return self.expand_wff(self._apply(rule, tree))


def constructor_heads(tree: AST) -> frozenset[tuple[str, str]]:
    if tree.is_variable:
        return frozenset()
    result = {(tree.sort, tree.head)}
    for argument in tree.args:
        result.update(constructor_heads(argument))
    return frozenset(result)
