#!/usr/bin/env python3
"""Generate source-native nominal semantic proofs from the checked MM DAG.

Unlike the old MM0 Lean output, this pass does not encode binders as arbitrary
host functions.  Set variables, wffs, and classes remain explicit nominal
objects (`Var`, `Wff`, and `Class`), and every generated theorem carries its
source `$d` contract as a finite-support hypothesis.

This bounded smoke emits the first thirty reachable source theorems plus the
quantified/DV theorem `a17d`.  Its proof bodies are regenerated from
`Statement.proof_ops`; no old Lean proof text is reused.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Mapping

from ast_replay import ASTReplayer, instantiate
from definitions import Expander, extract_rules
from mm_parser import Database, MMError, Statement
from syntax import AST, Grammar, SORTS, erase_primitive_provenance


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
SOURCE = (
    WORKSPACE
    / "work/mm0_definition_conversion_2026-08-21/"
    "binding_metadata/set_mm_repo/nf.mm"
)
OUTPUT = HERE / "generated" / "SourceNativeSmoke.lean"
MANIFEST = HERE / "generated" / "source_native_smoke_manifest.json"
THEOREM_LIMIT = 30

LOGICAL_LEAVES = frozenset({"ax-mp", "ax-1", "ax-2", "ax-3", "ax-gen", "ax-17"})


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def safe(name: str) -> str:
    result = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if not result or result[0].isdigit():
        result = "n_" + result
    return result


def same_print(left: AST, right: AST) -> bool:
    return left == right or erase_primitive_provenance(left) == erase_primitive_provenance(right)


@dataclass(frozen=True, slots=True)
class StackEntry:
    ast: AST
    proof: str | None


class Emitter:
    def __init__(self, database: Database, replayer: ASTReplayer, expander: Expander) -> None:
        self.database = database
        self.replayer = replayer
        self.expander = expander
        self.normalized: dict[str, AST] = {}

    def normalize(self, tree: AST) -> AST:
        if tree.sort == "wff":
            return self.expander.expand_wff(tree)
        if tree.sort == "class":
            return self.expander.expand_class(tree)
        return tree

    def normalized_schema(self, label: str) -> AST:
        old = self.normalized.get(label)
        if old is not None:
            return old
        result = self.normalize(self.replayer.schema[label])
        self.normalized[label] = result
        return result

    def expr(self, tree: AST) -> str:
        """Emit one normalized nominal expression."""

        if tree.is_variable:
            return safe(tree.variable_name)
        args = [self.expr(argument) for argument in tree.args]
        if tree.sort == "class":
            if tree.head == "cv" and len(args) == 1:
                return f"(.cv {args[0]})"
            if tree.head == "cab" and len(args) == 2:
                return f"(.cab {args[0]} {args[1]})"
            raise MMError(f"non-core class expression {tree.sexpr()}")
        if tree.sort != "wff":
            raise MMError(f"cannot emit sort {tree.sort}: {tree.sexpr()}")
        if tree.head == "wbot" and not args:
            return ".falsum"
        if tree.head == "wn" and len(args) == 1:
            return f"(.neg {args[0]})"
        if tree.head == "wi" and len(args) == 2:
            return f"(.imp {args[0]} {args[1]})"
        if tree.head == "wal" and len(args) == 2:
            return f"(.all {args[0]} {args[1]})"
        if tree.head == "weq" and len(args) == 2:
            return f"(.objEq {args[0]} {args[1]})"
        if tree.head == "wel" and len(args) == 2:
            return f"(.objMem {args[0]} {args[1]})"
        if tree.head == "wceq" and len(args) == 2:
            return f"(.classEq {args[0]} {args[1]})"
        if tree.head == "wcel" and len(args) == 2:
            return f"(.classMem {args[0]} {args[1]})"
        raise MMError(f"non-core wff expression {tree.sexpr()}")

    def sort_type(self, sort: str) -> str:
        return {"setvar": "Var", "wff": "Wff", "class": "Class"}[sort]

    def support(self, name: str, sort: str) -> str:
        ident = safe(name)
        if sort == "setvar":
            return f"({{{ident}}} : Finset Var)"
        return f"{ident}.vars"

    def dv_name(self, left: str, right: str) -> str:
        return f"dv_{safe(left)}_{safe(right)}"

    def dv_type(self, left: str, right: str) -> str:
        left_sort = self.database.variable_type[left]
        right_sort = self.database.variable_type[right]
        left_id = safe(left)
        right_id = safe(right)
        if left_sort == "setvar" and right_sort == "setvar":
            return f"{left_id} ≠ {right_id}"
        if left_sort == "setvar":
            return f"{left_id} ∉ {self.support(right, right_sort)}"
        if right_sort == "setvar":
            return f"{right_id} ∉ {self.support(left, left_sort)}"
        return f"Disjoint {self.support(left, left_sort)} {self.support(right, right_sort)}"

    def theorem_signature(self, statement: Statement) -> tuple[list[str], dict[str, str]]:
        params = ["{S : Fol.Structure LNF}",
                  "(hNF : Fol.all_realize_sentence S LiteralHailperinNF)"]
        float_hyps = [hyp for hyp in statement.hyps if hyp.kind == "$f"]
        env: dict[str, str] = {}
        for hyp in float_hyps:
            sort, name = hyp.expr
            params.append(f"({safe(name)} : {self.sort_type(sort)})")
            env[name] = safe(name)
        for left, right in sorted(statement.dv):
            params.append(
                f"({self.dv_name(left, right)} : {self.dv_type(left, right)})"
            )
        for hyp in statement.hyps:
            if hyp.kind != "$e":
                continue
            formula = self.normalize(self.replayer.schema[hyp.label])
            params.append(
                f"(hyp_{safe(hyp.label)} : Wff.Valid S {self.expr(formula)})"
            )
        return params, env

    def logical_leaf(
        self,
        label: str,
        substitution: Mapping[str, AST],
        essential_proofs: list[str],
    ) -> str:
        actual = {name: self.expr(self.normalize(tree)) for name, tree in substitution.items()}
        if label == "ax-mp":
            return f"Wff.valid_mp {essential_proofs[0]} {essential_proofs[1]}"
        if label == "ax-1":
            return f"NFChoice.LogicalSemantics.Wff.valid_ax_1 (S := S) {actual['ph']} {actual['ps']}"
        if label == "ax-2":
            return (
                "NFChoice.LogicalSemantics.Wff.valid_ax_2 (S := S) "
                f"{actual['ph']} {actual['ps']} {actual['ch']}"
            )
        if label == "ax-3":
            return f"NFChoice.LogicalSemantics.Wff.valid_ax_3 (S := S) {actual['ph']} {actual['ps']}"
        if label == "ax-gen":
            return f"Wff.valid_generalization {essential_proofs[0]} {actual['x']}"
        if label == "ax-17":
            return (
                "NFChoice.SemanticCore.Wff.valid_ax17_of_not_mem_vars "
                f"(S := S) {actual['ph']} {actual['x']} "
                "(by simp_all [Wff.vars, Class.vars])"
            )
        raise MMError(f"unsupported logical leaf {label}")

    def theorem_call(
        self,
        rule: Statement,
        substitution: Mapping[str, AST],
        essential_proofs: list[str],
    ) -> str:
        arguments = [f"g_{safe(rule.label)} (S := S) hNF"]
        for hyp in rule.hyps:
            if hyp.kind != "$f":
                continue
            variable = hyp.expr[1]
            arguments.append(self.expr(self.normalize(substitution[variable])))
        for _left, _right in sorted(rule.dv):
            arguments.append("(by simp_all [Wff.vars, Class.vars])")
        arguments.extend(essential_proofs)
        return " ".join(arguments)

    def emit_theorem(self, label: str, available: frozenset[str]) -> str:
        theorem = self.database.statements[label]
        if theorem.kind != "$p":
            raise MMError(f"{label} is not a theorem")
        params, _env = self.theorem_signature(theorem)
        conclusion = self.normalized_schema(label)
        lines = [
            f"theorem g_{safe(label)}",
            "    " + " ".join(params) + " :",
            f"    Wff.Valid S {self.expr(conclusion)} := by",
        ]
        stack: list[StackEntry] = []
        saved: list[StackEntry] = []
        proof_index = 0
        for op in theorem.proof_ops:
            if op.kind == "save":
                if not stack:
                    raise MMError(f"save on empty stack in {label}")
                saved.append(stack[-1])
                continue
            if op.kind == "saved":
                stack.append(saved[int(op.value)])
                continue
            reference = str(op.value)
            rule = self.database.statements[reference]
            if rule.kind == "$f":
                stack.append(StackEntry(self.replayer.schema[reference], None))
                continue
            if rule.kind == "$e":
                stack.append(
                    StackEntry(
                        self.replayer.schema[reference], f"hyp_{safe(reference)}"
                    )
                )
                continue
            arity = len(rule.hyps)
            arguments = stack[-arity:] if arity else []
            if arity:
                del stack[-arity:]
            substitution: dict[str, AST] = {}
            essential_proofs: list[str] = []
            for hyp, actual_entry in zip(rule.hyps, arguments):
                if hyp.kind == "$f":
                    substitution[hyp.expr[1]] = actual_entry.ast
                else:
                    if actual_entry.proof is None:
                        raise MMError(f"missing essential proof at {reference} in {label}")
                    expected = instantiate(self.replayer.schema[hyp.label], substitution)
                    if not same_print(expected, actual_entry.ast):
                        raise MMError(f"essential AST mismatch at {reference} in {label}")
                    essential_proofs.append(actual_entry.proof)
            result = instantiate(self.replayer.schema[reference], substitution)
            if rule.typecode != "|-":
                stack.append(StackEntry(result, None))
                continue
            normalized_result = self.normalize(result)
            expected_callee = instantiate(self.normalized_schema(reference), substitution)
            expected_callee = self.normalize(expected_callee)
            if normalized_result != expected_callee:
                raise MMError(
                    f"normalization/substitution does not commute at {reference} in {label}: "
                    f"{normalized_result.sexpr()} != {expected_callee.sexpr()}"
                )
            if rule.kind == "$a":
                if reference not in LOGICAL_LEAVES:
                    raise MMError(f"unsupported axiom leaf {reference} in bounded smoke")
                proof_term = self.logical_leaf(reference, substitution, essential_proofs)
            else:
                if reference not in available:
                    raise MMError(f"unavailable theorem {reference} in {label}")
                proof_term = self.theorem_call(rule, substitution, essential_proofs)
            node = f"p{proof_index:03d}"
            proof_index += 1
            lines.extend(
                [
                    f"  have {node} : Wff.Valid S {self.expr(normalized_result)} := by",
                    f"    exact {proof_term}",
                ]
            )
            stack.append(StackEntry(result, node))
        if len(stack) != 1 or stack[0].proof is None:
            raise MMError(f"bad final source-native stack for {label}")
        normalized_root = self.normalize(stack[0].ast)
        if normalized_root != conclusion:
            raise MMError(f"source-native conclusion mismatch for {label}")
        lines.append(f"  exact {stack[0].proof}")
        return "\n".join(lines)


def main() -> None:
    sys.setrecursionlimit(200_000)
    database = Database()
    database.parse(SOURCE)
    grammar = Grammar(database)
    replayer = ASTReplayer(database, grammar)
    replayer.replay_closure("nchoice")
    expander = Expander(extract_rules(database, replayer))
    emitter = Emitter(database, replayer, expander)
    reachable = [
        statement.label
        for statement in database.dependency_closure("nchoice")
        if statement.kind == "$p"
    ]
    labels = reachable[:THEOREM_LIMIT]
    if "a17d" not in labels:
        labels.append("a17d")
    available: set[str] = set()
    theorem_texts: list[str] = []
    for label in labels:
        theorem_texts.append(emitter.emit_theorem(label, frozenset(available)))
        available.add(label)
    header = """import LogicalSemantics.Basic
import ReplaySupport.Basic

namespace NFChoice.Compiler.SourceNativeSmoke

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport

"""
    footer = """

#print axioms g_mp2b
#print axioms g_a1dd
#print axioms g_a17d

end NFChoice.Compiler.SourceNativeSmoke
"""
    text = header + "\n\n".join(theorem_texts) + footer
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(text, encoding="utf-8", newline="\n")
    record = {
        "status": "GENERATED_UNCHECKED",
        "source": str(SOURCE),
        "source_sha256": sha256(SOURCE.read_bytes()),
        "theorem_count": len(labels),
        "labels": labels,
        "proof_origin": "regenerated from checked Statement.proof_ops",
        "binder_representation": "explicit nominal Var/Wff/Class",
        "dv_contract": "sort-specific finite support",
        "output": str(OUTPUT),
        "output_bytes": len(text.encode("utf-8")),
        "output_sha256": sha256(text.encode("utf-8")),
    }
    MANIFEST.write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
