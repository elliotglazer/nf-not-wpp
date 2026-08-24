#!/usr/bin/env python3
"""Recover typed ASTs by replaying the checked Metamath proofs.

Parsing every expanded theorem conclusion is unnecessarily expensive: some
late ``nf.mm`` conclusions contain hundreds of tokens of generated class
notation.  Metamath proofs already carry their parse construction.  This pass
therefore parses only axiom/definition schemas and essential hypotheses, then
instantiates previously recovered theorem ASTs while replaying each proof.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Iterable, Mapping

from mm_parser import Database, MMError, Statement
from syntax import AST, Grammar, SORTS, erase_primitive_provenance


@lru_cache(maxsize=None)
def _instantiate_cached(tree: AST, substitution: tuple[tuple[str, AST], ...]) -> AST:
    mapping = dict(substitution)

    def visit(node: AST) -> AST:
        if node.is_variable:
            replacement = mapping.get(node.variable_name)
            return replacement if replacement is not None else node
        return AST(node.sort, node.head, tuple(visit(arg) for arg in node.args))

    return visit(tree)


def instantiate(tree: AST, substitution: Mapping[str, AST]) -> AST:
    return _instantiate_cached(tree, tuple(sorted(substitution.items())))


@dataclass(frozen=True, slots=True)
class ASTReplayAudit:
    assertion_count: int
    parsed_axiom_schemas: int
    parsed_essential_hypotheses: int
    replayed_theorems: int
    provenance_recanonicalizations: int
    endpoint: str
    endpoint_ast: AST


class ASTReplayer:
    def __init__(self, database: Database, grammar: Grammar) -> None:
        self.database = database
        self.grammar = grammar
        self.schema: dict[str, AST] = {}
        self.parsed_axioms: set[str] = set()
        self.parsed_essentials: set[str] = set()
        self.recanonicalizations: list[
            tuple[str, str, str, str, str]
        ] = []

    def _check_same_printed_parse(
        self,
        theorem: str,
        rule: str,
        position: str,
        expected: AST,
        actual: AST,
    ) -> None:
        if expected == actual:
            return
        if erase_primitive_provenance(expected) != erase_primitive_provenance(actual):
            raise MMError(
                f"non-alias AST mismatch in {theorem} at {rule}/{position}: "
                f"{expected.sexpr()} != {actual.sexpr()}"
            )
        self.recanonicalizations.append(
            (theorem, rule, position, expected.sexpr(), actual.sexpr())
        )

    def _schema_for_leaf(self, label: str) -> AST:
        old = self.schema.get(label)
        if old is not None:
            return old
        statement = self.database.statements[label]
        if statement.kind == "$f":
            if statement.typecode not in SORTS or len(statement.expr) != 2:
                raise MMError(f"malformed floating hypothesis {label}")
            result = AST.variable(statement.typecode, statement.expr[1])
        elif statement.kind == "$e":
            result = self.grammar.parse_hypothesis(statement.expr)
            self.parsed_essentials.add(label)
        elif statement.kind == "$a":
            result = self.grammar.parse_statement(statement)
            self.parsed_axioms.add(label)
        elif statement.kind == "$p":
            raise MMError(f"theorem schema {label} has not been replayed yet")
        else:
            raise MMError(f"unsupported statement kind at {label}: {statement.kind}")
        self.schema[label] = result
        return result

    def replay_theorem(self, label: str) -> AST:
        theorem = self.database.statements[label]
        if theorem.kind != "$p":
            raise MMError(f"{label} is not a theorem")
        # nf.mm deliberately proves these two syntax constructors from the
        # class grammar to avoid parser overloading.  Semantically they remain
        # primitive object equality/membership, so retain their source heads
        # instead of replacing them by the proof's wceq/wcel construction.
        if label in {"weq", "wel"}:
            result = self.grammar.parse_statement(theorem)
            if result.head != label:
                raise MMError(f"failed to retain primitive syntax provenance at {label}")
            self.schema[label] = result
            return result
        stack: list[AST] = []
        saved: list[AST] = []
        for op in theorem.proof_ops:
            if op.kind == "save":
                if not stack:
                    raise MMError(f"AST save on empty stack in {label}")
                saved.append(stack[-1])
                continue
            if op.kind == "saved":
                index = int(op.value)
                if index < 0 or index >= len(saved):
                    raise MMError(f"bad AST saved-step index {index} in {label}")
                stack.append(saved[index])
                continue
            reference = str(op.value)
            rule = self.database.statements[reference]
            if rule.kind in {"$f", "$e"}:
                stack.append(self._schema_for_leaf(reference))
                continue
            arity = len(rule.hyps)
            if len(stack) < arity:
                raise MMError(f"AST stack underflow at {reference} in {label}")
            arguments = stack[-arity:] if arity else []
            if arity:
                del stack[-arity:]
            substitution: dict[str, AST] = {}
            for hyp, actual in zip(rule.hyps, arguments):
                if hyp.kind != "$f":
                    continue
                variable = hyp.expr[1]
                if actual.sort != hyp.expr[0]:
                    raise MMError(
                        f"AST sort mismatch at {reference} in {label}: "
                        f"{actual.sort} != {hyp.expr[0]}"
                    )
                previous = substitution.get(variable)
                if previous is not None and previous != actual:
                    raise MMError(
                        f"AST substitution mismatch for {variable} at {reference}"
                    )
                substitution[variable] = actual
            for hyp, actual in zip(rule.hyps, arguments):
                if hyp.kind != "$e":
                    continue
                expected_hyp = instantiate(
                    self._schema_for_leaf(hyp.label), substitution
                )
                self._check_same_printed_parse(
                    label, reference, hyp.label, expected_hyp, actual
                )
            schema = self.schema.get(reference)
            if schema is None:
                schema = self._schema_for_leaf(reference)
            stack.append(instantiate(schema, substitution))
        if len(stack) != 1:
            raise MMError(f"AST proof {label} leaves stack size {len(stack)}")
        result = stack[0]
        expected_sort = "wff" if theorem.typecode == "|-" else theorem.typecode
        if result.sort != expected_sort:
            raise MMError(
                f"AST theorem {label} has sort {result.sort}, expected {expected_sort}"
            )
        # Small conclusions are cheap to parse independently, giving a useful
        # cross-check of proof-driven reconstruction without hitting the large
        # generated class expressions later in nf.mm.
        if len(theorem.expr) <= 80:
            parsed = self.grammar.parse_statement(theorem)
            self._check_same_printed_parse(
                label, label, "conclusion", parsed, result
            )
        self.schema[label] = result
        return result

    def replay_closure(self, endpoint: str) -> ASTReplayAudit:
        closure = self.database.dependency_closure(endpoint)
        theorem_count = 0
        for statement in closure:
            if statement.kind == "$a":
                self._schema_for_leaf(statement.label)
            elif statement.kind == "$p":
                self.replay_theorem(statement.label)
                theorem_count += 1
        endpoint_ast = self.schema[endpoint]
        return ASTReplayAudit(
            assertion_count=len(closure),
            parsed_axiom_schemas=len(self.parsed_axioms),
            parsed_essential_hypotheses=len(self.parsed_essentials),
            replayed_theorems=theorem_count,
            provenance_recanonicalizations=len(self.recanonicalizations),
            endpoint=endpoint,
            endpoint_ast=endpoint_ast,
        )
