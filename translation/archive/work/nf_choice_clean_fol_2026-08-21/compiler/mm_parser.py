#!/usr/bin/env python3
"""Small deterministic Metamath parser/verifier used by the NF compiler.

The implementation deliberately keeps the source proof program.  It does not
invoke ``metamath.exe`` and it does not trust ``$p`` statements: every proof is
decoded and replayed while the database is parsed.

Only standard Metamath database features used by ``nf.mm`` are implemented.
The resulting statement graph is a convenient, stable frontend for later
translation passes; none of the later passes need to recover dependencies from
formatted source text.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import re
from typing import Iterable, Iterator, Mapping, Sequence


TOKEN = re.compile(r"\$\(|\$\)|\$\{|\$\}|\$\[|\$\]|\$[cvfedap=.]|\S+")
TYPECODES = frozenset({"setvar", "class", "wff", "|-"})


class MMError(RuntimeError):
    """A deterministic source or proof error."""


@dataclass(frozen=True, slots=True)
class Hypothesis:
    label: str
    kind: str
    expr: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class ProofOp:
    kind: str  # ``label``, ``save``, or ``saved``
    value: str | int | None


@dataclass(frozen=True, slots=True)
class Application:
    """One checked proof-stack application.

    ``substitution`` contains token expressions without their typecodes.  It is
    retained only when ``Database.replay(..., record=True)`` is requested.
    """

    label: str
    arguments: tuple[int, ...]
    substitution: tuple[tuple[str, tuple[str, ...]], ...]
    result: tuple[str, ...]


@dataclass(slots=True)
class Statement:
    label: str
    kind: str
    expr: tuple[str, ...]
    hyps: tuple[Hypothesis, ...]
    dv: frozenset[tuple[str, str]]
    proof_dv: frozenset[tuple[str, str]]
    file: str
    ordinal: int
    proof_tokens: tuple[str, ...] = ()
    proof_ops: tuple[ProofOp, ...] = ()
    dependencies: frozenset[str] = frozenset()

    @property
    def typecode(self) -> str:
        if not self.expr:
            raise MMError(f"empty expression at {self.label}")
        return self.expr[0]


@dataclass(slots=True)
class _Scope:
    floating: list[Hypothesis] = field(default_factory=list)
    essential: list[Hypothesis] = field(default_factory=list)
    dv: set[tuple[str, str]] = field(default_factory=set)

    def copy(self) -> "_Scope":
        return _Scope(list(self.floating), list(self.essential), set(self.dv))


@dataclass(frozen=True, slots=True)
class Replay:
    expression: tuple[str, ...]
    applications: tuple[Application, ...]
    root: int


def _ordered_pair(x: str, y: str) -> tuple[str, str]:
    return (x, y) if x < y else (y, x)


def tokenize_text(text: str) -> tuple[str, ...]:
    """Tokenize a Metamath file and remove comments."""

    raw = TOKEN.findall(text)
    out: list[str] = []
    i = 0
    while i < len(raw):
        token = raw[i]
        if token == "$(":
            i += 1
            while i < len(raw) and raw[i] != "$)":
                i += 1
            if i == len(raw):
                raise MMError("unterminated Metamath comment")
            i += 1
            continue
        if token == "$)":
            raise MMError("comment terminator outside comment")
        out.append(token)
        i += 1
    return tuple(out)


def decode_compressed(
    proof: Sequence[str], mandatory_labels: Sequence[str]
) -> tuple[ProofOp, ...]:
    """Decode a Metamath compressed proof into explicit stack operations."""

    if not proof or proof[0] != "(":
        return tuple(ProofOp("label", token) for token in proof)
    try:
        close = proof.index(")")
    except ValueError as exc:
        raise MMError("unterminated compressed label list") from exc
    refs = tuple(mandatory_labels) + tuple(proof[1:close])
    ops: list[ProofOp] = []
    acc = 0
    for char in "".join(proof[close + 1 :]):
        if "U" <= char <= "Y":
            acc = 5 * acc + ord(char) - ord("U") + 1
        elif "A" <= char <= "T":
            number = 20 * acc + ord(char) - ord("A") + 1
            acc = 0
            if number <= len(refs):
                ops.append(ProofOp("label", refs[number - 1]))
            else:
                ops.append(ProofOp("saved", number - len(refs) - 1))
        elif char == "Z":
            if acc:
                raise MMError("unfinished compressed integer before save")
            ops.append(ProofOp("save", None))
        elif char == "?":
            raise MMError("incomplete proof contains '?' marker")
        else:
            raise MMError(f"invalid compressed proof character {char!r}")
    if acc:
        raise MMError("unfinished compressed integer at end of proof")
    return tuple(ops)


class Database:
    """Parsed and proof-checked Metamath database."""

    def __init__(self) -> None:
        self.constants: set[str] = set()
        self.variables: set[str] = set()
        self.variable_type: dict[str, str] = {}
        self.statements: dict[str, Statement] = {}
        self.order: list[str] = []
        self._scopes: list[_Scope] = [_Scope()]
        self._files: set[Path] = set()

    @property
    def scope(self) -> _Scope:
        return self._scopes[-1]

    def _mandatory(self, expr: Sequence[str]) -> tuple[Hypothesis, ...]:
        used = {token for token in expr if token in self.variables}
        for hyp in self.scope.essential:
            used.update(token for token in hyp.expr if token in self.variables)
        floating = [
            hyp
            for hyp in self.scope.floating
            if len(hyp.expr) == 2 and hyp.expr[1] in used
        ]
        return tuple(floating + self.scope.essential)

    @staticmethod
    def substitute(
        expr: Sequence[str], substitution: Mapping[str, Sequence[str]]
    ) -> tuple[str, ...]:
        out: list[str] = []
        for token in expr:
            out.extend(substitution.get(token, (token,)))
        return tuple(out)

    def _add_statement(self, statement: Statement) -> None:
        if statement.label in self.statements:
            raise MMError(f"duplicate label {statement.label}")
        self.statements[statement.label] = statement
        self.order.append(statement.label)

    def parse(self, path: Path) -> None:
        """Parse ``path`` (and any includes) and verify every ``$p`` proof."""

        self._parse_file(path.resolve())

    def _parse_file(self, path: Path) -> None:
        if path in self._files:
            return
        self._files.add(path)
        tokens = tokenize_text(path.read_text(encoding="utf-8"))
        i = 0
        while i < len(tokens):
            token = tokens[i]
            if token == "$[":
                if i + 2 >= len(tokens) or tokens[i + 2] != "$]":
                    raise MMError(f"malformed include in {path}")
                include = (path.parent / tokens[i + 1]).resolve()
                if not include.exists():
                    raise MMError(f"missing include {include}")
                self._parse_file(include)
                i += 3
                continue
            if token == "${":
                self._scopes.append(self.scope.copy())
                i += 1
                continue
            if token == "$}":
                if len(self._scopes) == 1:
                    raise MMError(f"unmatched $}} in {path}")
                self._scopes.pop()
                i += 1
                continue
            if token in {"$c", "$v", "$d"}:
                directive = token
                i += 1
                values: list[str] = []
                while i < len(tokens) and tokens[i] != "$.":
                    values.append(tokens[i])
                    i += 1
                if i == len(tokens):
                    raise MMError(f"unterminated {directive} in {path}")
                i += 1
                if directive == "$c":
                    self.constants.update(values)
                elif directive == "$v":
                    self.variables.update(values)
                else:
                    for left_index, left in enumerate(values):
                        for right in values[left_index + 1 :]:
                            self.scope.dv.add(_ordered_pair(left, right))
                continue
            if i + 1 >= len(tokens) or tokens[i + 1] not in {
                "$f",
                "$e",
                "$a",
                "$p",
            }:
                raise MMError(f"unexpected token {token!r} in {path}")
            label = token
            kind = tokens[i + 1]
            i += 2
            expression: list[str] = []
            while i < len(tokens) and tokens[i] not in {"$=", "$."}:
                expression.append(tokens[i])
                i += 1
            if i == len(tokens):
                raise MMError(f"unterminated statement {label}")
            proof: list[str] = []
            if tokens[i] == "$=":
                if kind != "$p":
                    raise MMError(f"proof marker on non-theorem {label}")
                i += 1
                while i < len(tokens) and tokens[i] != "$.":
                    proof.append(tokens[i])
                    i += 1
                if i == len(tokens):
                    raise MMError(f"unterminated proof {label}")
            elif kind == "$p":
                raise MMError(f"missing proof for {label}")
            i += 1
            expr = tuple(expression)
            if not expr:
                raise MMError(f"empty expression for {label}")
            ordinal = len(self.order)
            if kind in {"$f", "$e"}:
                hyp = Hypothesis(label, kind, expr)
                statement = Statement(
                    label,
                    kind,
                    expr,
                    (),
                    frozenset(),
                    frozenset(self.scope.dv),
                    str(path),
                    ordinal,
                )
                self._add_statement(statement)
                if kind == "$f":
                    if len(expr) != 2 or expr[0] not in TYPECODES:
                        raise MMError(f"bad floating hypothesis {label}: {expr}")
                    old_type = self.variable_type.get(expr[1])
                    if old_type is not None and old_type != expr[0]:
                        raise MMError(
                            f"variable {expr[1]} changes type {old_type} -> {expr[0]}"
                        )
                    self.variable_type[expr[1]] = expr[0]
                    self.scope.floating.append(hyp)
                else:
                    self.scope.essential.append(hyp)
                continue
            hyps = self._mandatory(expr)
            used = {token for token in expr if token in self.variables}
            for hyp in hyps:
                used.update(token for token in hyp.expr if token in self.variables)
            dv = frozenset(
                pair
                for pair in self.scope.dv
                if pair[0] in used and pair[1] in used
            )
            ops: tuple[ProofOp, ...] = ()
            dependencies: frozenset[str] = frozenset()
            if kind == "$p":
                ops = decode_compressed(proof, [hyp.label for hyp in hyps])
                dependencies = frozenset(
                    str(op.value)
                    for op in ops
                    if op.kind == "label"
                    and str(op.value) in self.statements
                    and self.statements[str(op.value)].kind in {"$a", "$p"}
                )
            statement = Statement(
                label,
                kind,
                expr,
                hyps,
                dv,
                frozenset(self.scope.dv),
                str(path),
                ordinal,
                tuple(proof),
                ops,
                dependencies,
            )
            self._add_statement(statement)
            if kind == "$p":
                replay = self.replay(label, record=False)
                if replay.expression != expr:
                    raise MMError(
                        f"wrong conclusion for {label}: {replay.expression} != {expr}"
                    )
        if len(self._scopes) != 1:
            raise MMError(f"unclosed scope after {path}")

    def replay(self, label: str, *, record: bool = True) -> Replay:
        """Replay one proof, optionally retaining its local application DAG."""

        target = self.statements[label]
        if target.kind != "$p":
            raise MMError(f"{label} is not a theorem")
        expression_stack: list[tuple[str, ...]] = []
        node_stack: list[int] = []
        saved_expressions: list[tuple[str, ...]] = []
        saved_nodes: list[int] = []
        applications: list[Application] = []
        for op in target.proof_ops:
            if op.kind == "save":
                if not expression_stack:
                    raise MMError(f"save on empty stack in {label}")
                saved_expressions.append(expression_stack[-1])
                saved_nodes.append(node_stack[-1])
                continue
            if op.kind == "saved":
                index = int(op.value)
                if index < 0 or index >= len(saved_expressions):
                    raise MMError(f"bad saved-step index {index} in {label}")
                expression_stack.append(saved_expressions[index])
                node_stack.append(saved_nodes[index])
                continue
            reference = str(op.value)
            if reference not in self.statements:
                raise MMError(f"unknown proof label {reference} in {label}")
            rule = self.statements[reference]
            if rule.kind in {"$f", "$e"}:
                result = rule.expr
                expression_stack.append(result)
                if record:
                    node = len(applications)
                    applications.append(Application(reference, (), (), result))
                    node_stack.append(node)
                else:
                    node_stack.append(-1)
                continue
            arity = len(rule.hyps)
            if len(expression_stack) < arity:
                raise MMError(f"stack underflow applying {reference} in {label}")
            arguments = expression_stack[-arity:] if arity else []
            argument_nodes = node_stack[-arity:] if arity else []
            if arity:
                del expression_stack[-arity:]
                del node_stack[-arity:]
            substitution: dict[str, tuple[str, ...]] = {}
            for hyp, actual in zip(rule.hyps, arguments):
                if (
                    hyp.kind == "$f"
                    and len(hyp.expr) == 2
                    and hyp.expr[1] in self.variables
                ):
                    if not actual or actual[0] != hyp.expr[0]:
                        raise MMError(
                            f"type mismatch applying {reference} in {label}: "
                            f"{hyp.expr} vs {actual}"
                        )
                    variable = hyp.expr[1]
                    value = tuple(actual[1:])
                    previous = substitution.get(variable)
                    if previous is not None and previous != value:
                        raise MMError(
                            f"inconsistent substitution for {variable} at {reference}"
                        )
                    substitution[variable] = value
            for hyp, actual in zip(rule.hyps, arguments):
                expected = self.substitute(hyp.expr, substitution)
                if actual != expected:
                    raise MMError(
                        f"hypothesis mismatch applying {reference} in {label}: "
                        f"expected {expected}, got {actual}"
                    )
            for left, right in rule.dv:
                left_variables = {
                    token
                    for token in substitution.get(left, (left,))
                    if token in self.variables
                }
                right_variables = {
                    token
                    for token in substitution.get(right, (right,))
                    if token in self.variables
                }
                for actual_left in left_variables:
                    for actual_right in right_variables:
                        pair = _ordered_pair(actual_left, actual_right)
                        if actual_left == actual_right or pair not in target.proof_dv:
                            raise MMError(
                                f"DV violation applying {reference} in {label}: "
                                f"{left},{right} -> {actual_left},{actual_right}"
                            )
            result = self.substitute(rule.expr, substitution)
            expression_stack.append(result)
            if record:
                node = len(applications)
                applications.append(
                    Application(
                        reference,
                        tuple(argument_nodes),
                        tuple(sorted(substitution.items())),
                        result,
                    )
                )
                node_stack.append(node)
            else:
                node_stack.append(-1)
        if len(expression_stack) != 1:
            raise MMError(f"proof {label} leaves stack size {len(expression_stack)}")
        return Replay(
            expression_stack[0],
            tuple(applications),
            node_stack[0] if node_stack else -1,
        )

    def dependency_closure(self, endpoint: str) -> tuple[Statement, ...]:
        """Return the exact executed assertion closure in source order."""

        if endpoint not in self.statements:
            raise MMError(f"unknown endpoint {endpoint}")
        seen: set[str] = set()
        pending = [endpoint]
        while pending:
            label = pending.pop()
            if label in seen:
                continue
            statement = self.statements[label]
            if statement.kind not in {"$a", "$p"}:
                continue
            seen.add(label)
            if statement.kind == "$p":
                pending.extend(statement.dependencies - seen)
        return tuple(
            self.statements[label] for label in self.order if label in seen
        )


def assertion_counts(statements: Iterable[Statement]) -> dict[str, int]:
    result: dict[str, int] = {}
    for statement in statements:
        result[statement.kind] = result.get(statement.kind, 0) + 1
    return result
