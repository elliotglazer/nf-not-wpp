#!/usr/bin/env python3
"""Typed concrete-syntax parsing for ``nf.mm`` expressions.

Metamath itself stores expressions as flat token strings.  This module derives
the grammar from the database's ``setvar``/``class``/``wff`` assertions and
returns immutable constructor trees.

It is semantically important *not* to erase the proof-derived syntax heads
``weq`` and ``wel``.  They denote primitive object equality/membership, whereas
generic ``wceq`` and ``wcel`` denote the overloaded class operations.  Their
printed token strings overlap when both class operands are ``cv`` expressions.
The parser resolves a bare ambiguous source expression in favour of
``weq``/``wel``; proof-driven AST substitution retains a generic ``wceq`` or
``wcel`` head even when its class parameters later become ``cv``.  This is the
provenance distinction required by ``df-cleq`` and ``df-clel``.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Iterable, Iterator, Mapping, Sequence

from mm_parser import Database, MMError, Statement


SORTS = frozenset({"setvar", "class", "wff"})


@dataclass(frozen=True, slots=True)
class AST:
    sort: str
    head: str
    args: tuple["AST", ...] = ()

    @staticmethod
    def variable(sort: str, name: str) -> "AST":
        return AST(sort, f"@{name}")

    @property
    def is_variable(self) -> bool:
        return self.head.startswith("@") and not self.args

    @property
    def variable_name(self) -> str:
        if not self.is_variable:
            raise MMError(f"not a variable AST: {self}")
        return self.head[1:]

    def to_data(self) -> object:
        if self.is_variable:
            return {"sort": self.sort, "var": self.variable_name}
        return {
            "sort": self.sort,
            "head": self.head,
            "args": [argument.to_data() for argument in self.args],
        }

    def sexpr(self) -> str:
        if self.is_variable:
            return f"{self.sort}:{self.variable_name}"
        if not self.args:
            return self.head
        return f"({self.head} {' '.join(argument.sexpr() for argument in self.args)})"


@dataclass(frozen=True, slots=True)
class Slot:
    name: str
    sort: str


@dataclass(frozen=True, slots=True)
class Production:
    label: str
    result_sort: str
    pattern: tuple[str | Slot, ...]
    ordinal: int

    @property
    def slots(self) -> tuple[Slot, ...]:
        return tuple(item for item in self.pattern if isinstance(item, Slot))

    def to_data(self) -> object:
        return {
            "label": self.label,
            "result_sort": self.result_sort,
            "pattern": [
                {"slot": item.name, "sort": item.sort}
                if isinstance(item, Slot)
                else item
                for item in self.pattern
            ],
            "ordinal": self.ordinal,
        }


def erase_primitive_provenance(tree: AST) -> AST:
    """Return a key which forgets only the intended weq/wel print ambiguity."""

    args = tuple(erase_primitive_provenance(argument) for argument in tree.args)
    if tree.head == "weq":
        if len(args) != 2 or any(arg.sort != "setvar" for arg in args):
            raise MMError(f"malformed weq AST: {tree.sexpr()}")
        return AST(
            "wff",
            "wceq",
            (AST("class", "cv", (args[0],)), AST("class", "cv", (args[1],))),
        )
    if tree.head == "wel":
        if len(args) != 2 or any(arg.sort != "setvar" for arg in args):
            raise MMError(f"malformed wel AST: {tree.sexpr()}")
        return AST(
            "wff",
            "wcel",
            (AST("class", "cv", (args[0],)), AST("class", "cv", (args[1],))),
        )
    return AST(tree.sort, tree.head, args)


def primitive_score(tree: AST) -> int:
    """Prefer primitive atomic syntax when parsing an ambiguous flat string."""

    own = 1 if tree.head in {"weq", "wel"} else 0
    return own + sum(primitive_score(argument) for argument in tree.args)


class Grammar:
    """Grammar induced by typed syntax assertions."""

    def __init__(self, database: Database) -> None:
        self.database = database
        productions: list[Production] = []
        for label in database.order:
            statement = database.statements[label]
            if statement.kind not in {"$a", "$p"}:
                continue
            if statement.typecode not in SORTS:
                continue
            if statement.hyps and any(hyp.kind == "$e" for hyp in statement.hyps):
                raise MMError(f"syntax assertion {label} has an essential hypothesis")
            pattern: list[str | Slot] = []
            for token in statement.expr[1:]:
                sort = database.variable_type.get(token)
                pattern.append(Slot(token, sort) if sort in SORTS else token)
            productions.append(
                Production(label, statement.typecode, tuple(pattern), statement.ordinal)
            )
        self.productions = tuple(productions)
        self.by_sort: dict[str, tuple[Production, ...]] = {
            sort: tuple(p for p in self.productions if p.result_sort == sort)
            for sort in sorted(SORTS)
        }

    def parse(self, sort: str, tokens: Sequence[str]) -> AST:
        """Parse one expression, rejecting genuine ambiguity."""

        if sort not in SORTS:
            raise MMError(f"unknown syntax sort {sort}")
        source = tuple(tokens)
        active: set[tuple[str, int, int]] = set()

        @lru_cache(maxsize=None)
        def parse_span(wanted: str, begin: int, end: int) -> tuple[AST, ...]:
            key = (wanted, begin, end)
            if key in active:
                return ()
            active.add(key)
            found: list[AST] = []
            if end == begin + 1:
                token = source[begin]
                if self.database.variable_type.get(token) == wanted:
                    found.append(AST.variable(wanted, token))
            for production in self.by_sort[wanted]:
                bindings: dict[str, AST] = {}

                def match(
                    pattern_index: int, position: int, children: tuple[AST, ...]
                ) -> None:
                    if len(found) >= 128:
                        raise MMError(
                            f"parse forest overflow for {wanted} {source[begin:end]}"
                        )
                    if pattern_index == len(production.pattern):
                        if position == end:
                            found.append(AST(wanted, production.label, children))
                        return
                    item = production.pattern[pattern_index]
                    if isinstance(item, str):
                        if position < end and source[position] == item:
                            match(pattern_index + 1, position + 1, children)
                        return
                    remaining_items = len(production.pattern) - pattern_index - 1
                    maximum = end - remaining_items
                    for split in range(position + 1, maximum + 1):
                        for child in parse_span(item.sort, position, split):
                            old = bindings.get(item.name)
                            if old is not None and old != child:
                                continue
                            if old is None:
                                bindings[item.name] = child
                            match(pattern_index + 1, split, children + (child,))
                            if old is None:
                                del bindings[item.name]

                match(0, begin, ())
            active.remove(key)
            # Group only the intended weq/wel surface ambiguity, but retain the
            # primitive constructor in the chosen AST.  All other ambiguities
            # remain visible and are rejected by ``parse`` below.
            grouped: dict[AST, AST] = {}
            for tree in found:
                key_tree = erase_primitive_provenance(tree)
                previous = grouped.get(key_tree)
                if previous is None or (primitive_score(tree), tree.sexpr()) > (
                    primitive_score(previous),
                    previous.sexpr(),
                ):
                    grouped[key_tree] = tree
            return tuple(sorted(grouped.values(), key=lambda tree: tree.sexpr()))

        results = parse_span(sort, 0, len(source))
        if not results:
            raise MMError(f"cannot parse {sort}: {' '.join(source)}")
        if len(results) != 1:
            samples = "; ".join(tree.sexpr() for tree in results[:8])
            raise MMError(
                f"ambiguous {sort} expression {' '.join(source)}: {samples}"
            )
        return results[0]

    def parse_statement(self, statement: Statement) -> AST:
        """Parse a statement conclusion (dropping ``|-`` when present)."""

        if statement.typecode in SORTS:
            return self.parse(statement.typecode, statement.expr[1:])
        if statement.typecode == "|-":
            return self.parse("wff", statement.expr[1:])
        raise MMError(
            f"statement {statement.label} has unsupported typecode {statement.typecode}"
        )

    def parse_hypothesis(self, expression: Sequence[str]) -> AST:
        if not expression:
            raise MMError("empty hypothesis")
        if expression[0] in SORTS:
            return self.parse(expression[0], expression[1:])
        if expression[0] == "|-":
            return self.parse("wff", expression[1:])
        raise MMError(f"unsupported hypothesis typecode {expression[0]}")
