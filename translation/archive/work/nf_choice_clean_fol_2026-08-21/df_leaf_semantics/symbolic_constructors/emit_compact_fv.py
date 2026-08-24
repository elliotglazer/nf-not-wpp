#!/usr/bin/env python3
"""Generate kernel-checkable FV equations for all compact syntax heads."""

from __future__ import annotations

from dataclasses import dataclass
import argparse
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parents[1]
WORK = HERE.parents[2]
COMPILER = PACKAGE / "compiler"
sys.path.insert(0, str(COMPILER))

from ast_replay import ASTReplayer
from definitions import extract_rules
from mm_parser import Database, MMError
from syntax import AST, Grammar

SOURCE = WORK / "mm0_definition_conversion_2026-08-21/binding_metadata/set_mm_repo/nf.mm"
OUTPUT = HERE / "generated/CompactSyntaxFV.lean"


def safe(name: str) -> str:
    out = re.sub(r"[^A-Za-z0-9_]", "_", name)
    return "n_" + out if out and out[0].isdigit() else out


@dataclass(frozen=True, order=True)
class V:
    name: str
    dummy: bool = False


# Support expression tags: empty, atom, singleton, union, erase.
E = tuple
EMPTY: E = ("empty",)


def atom(name: str) -> E:
    return ("atom", name)


def singleton(v: V) -> E:
    return ("singleton", v)


def union(*items: E) -> E:
    flat: list[E] = []
    for item in items:
        if item == EMPTY:
            continue
        if item[0] == "union":
            flat.extend(item[1])
        else:
            flat.append(item)
    unique = tuple(sorted(set(flat), key=repr))
    if not unique:
        return EMPTY
    if len(unique) == 1:
        return unique[0]
    return ("union", unique)


def erase(expr: E, v: V) -> E:
    if expr == EMPTY:
        return EMPTY
    tag = expr[0]
    if tag == "union":
        return union(*(erase(item, v) for item in expr[1]))
    if tag == "atom":
        # Every generated dummy is outside every explicit Wff/Class FV support.
        return expr if v.dummy else ("erase", expr, v)
    if tag == "singleton":
        old: V = expr[1]
        if old == v:
            return EMPTY
        # Dummies are pairwise distinct and outside every explicit setvar.
        if old.dummy or v.dummy:
            return expr
        return ("erase", expr, v)
    if tag == "erase":
        if v.dummy:
            # The dummy is outside the original explicit support and hence
            # outside every visible erasure of that support.
            return expr
        if expr[2] == v:
            return expr
        return ("erase", expr, v)
    raise AssertionError(expr)


def subst(expr: E, supports: dict[str, E], vars_: dict[str, V]) -> E:
    tag = expr[0]
    if tag == "empty":
        return expr
    if tag == "atom":
        return supports[expr[1]]
    if tag == "singleton":
        return singleton(vars_[expr[1].name])
    if tag == "union":
        return union(*(subst(item, supports, vars_) for item in expr[1]))
    if tag == "erase":
        return erase(subst(expr[1], supports, vars_), vars_[expr[2].name])
    raise AssertionError(expr)


class FV:
    def __init__(self, rules) -> None:
        self.templates: dict[str, E] = {"wtru": EMPTY}
        self.rules = {rule.target_head: rule for rule in rules}

    def of(self, tree: AST, dummies: set[str]) -> E:
        if tree.is_variable:
            if tree.sort in {"wff", "class"}:
                return atom(tree.variable_name)
            raise MMError(f"bare setvar has no FV support: {tree.sexpr()}")
        h = tree.head
        if h == "cv":
            x = tree.args[0].variable_name
            return singleton(V(x, x in dummies))
        if h == "cab":
            x = tree.args[0].variable_name
            return erase(self.of(tree.args[1], dummies), V(x, x in dummies))
        if h == "wbot":
            return EMPTY
        if h == "wn":
            return self.of(tree.args[0], dummies)
        if h == "wi":
            return union(*(self.of(arg, dummies) for arg in tree.args))
        if h == "wal":
            x = tree.args[0].variable_name
            return erase(self.of(tree.args[1], dummies), V(x, x in dummies))
        if h in {"weq", "wel"}:
            return union(*(singleton(V(arg.variable_name, arg.variable_name in dummies)) for arg in tree.args))
        if h in {"wceq", "wcel"}:
            return union(*(self.of(arg, dummies) for arg in tree.args))
        template = self.templates.get(h)
        rule = self.rules.get(h)
        if template is None or rule is None:
            raise MMError(f"FV dependency not available: {h}")
        supports: dict[str, E] = {}
        vars_: dict[str, V] = {}
        for formal, actual in zip(rule.lhs.args, tree.args):
            if formal.sort == "setvar":
                name = actual.variable_name
                vars_[formal.variable_name] = V(name, name in dummies)
            else:
                supports[formal.variable_name] = self.of(actual, dummies)
        return subst(template, supports, vars_)


def lean(expr: E) -> str:
    tag = expr[0]
    if tag == "empty":
        return "(∅ : Finset Var)"
    if tag == "atom":
        return f"{safe(expr[1])}.fv"
    if tag == "singleton":
        return f"({{{safe(expr[1].name)}}} : Finset Var)"
    if tag == "union":
        return " ∪ ".join(f"({lean(item)})" for item in expr[1])
    if tag == "erase":
        return f"({lean(expr[1])}).erase {safe(expr[2].name)}"
    raise AssertionError(expr)


def support_of_args(args: tuple[AST, ...]) -> str:
    parts = []
    for arg in args:
        name = safe(arg.variable_name)
        parts.append(f"({{{name}}} : Finset Var)" if arg.sort == "setvar" else f"{name}.fv")
    return " ∪ ".join(parts) if parts else "(∅ : Finset Var)"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--explicit", action="store_true")
    args_cli = parser.parse_args()
    module = "CompactSyntaxFVExplicit" if args_cli.explicit else "CompactSyntaxFV"
    output = HERE / f"generated/{module}.lean"
    manifest_output = HERE / f"generated/{module}.json"
    sys.setrecursionlimit(200_000)
    db = Database()
    db.parse(SOURCE)
    replay = ASTReplayer(db, Grammar(db))
    for statement in db.dependency_closure("nchoice"):
        if statement.kind == "$a":
            replay._schema_for_leaf(statement.label)
    rules = extract_rules(db, replay)
    fv = FV(rules)
    theorem_blocks = []
    map_lines = []
    for rule in rules:
        dummy_names = {name for _sort, name in rule.dummy_variables}
        template = fv.of(rule.rhs, dummy_names)
        if any(v.dummy for node in walk_expr(template) for v in vars_in_node(node)):
            raise MMError(f"dummy leaked from FV template {rule.label}: {template}")
        fv.templates[rule.target_head] = template

        sort_types = {"setvar": "Var", "wff": "Wff", "class": "Class"}
        params = " ".join(
            f"({safe(arg.variable_name)} : {sort_types[arg.sort]})"
            for arg in rule.lhs.args
        )
        args = " ".join(safe(arg.variable_name) for arg in rule.lhs.args)
        result = "Wff" if rule.target_sort == "wff" else "Class"
        support = support_of_args(rule.lhs.args)
        facts = []
        for i, (_sort, name) in enumerate(rule.dummy_variables):
            facts.append(
                f"  have fresh_{safe(name)} : freshVar ({support}) {i} ∉ ({support}) :=\n"
                f"    freshVar_not_mem ({support}) {i}\n"
                f"  simp only [Finset.mem_union, Finset.mem_singleton] at fresh_{safe(name)}"
            )
        for i in range(len(rule.dummy_variables)):
            for j in range(i + 1, len(rule.dummy_variables)):
                ni = safe(rule.dummy_variables[i][1])
                nj = safe(rule.dummy_variables[j][1])
                facts.append(
                    f"  have distinct_{ni}_{nj} : freshVar ({support}) {i} ≠ freshVar ({support}) {j} :=\n"
                    f"    freshVar_injective ({support}) (by decide)"
                )
        dependencies = sorted({
            node.head
            for node in walk_ast(rule.rhs)
            if (not node.is_variable) and node.head in fv.templates and node.head != "wtru"
        })
        explicit_deps = ", ".join(f"fv_syn_{safe(head)}" for head in dependencies)
        simp_items = ", ".join(filter(None, [
            f"syn_{safe(rule.target_head)}",
            explicit_deps,
            "Wff.fv, Class.fv, Wff.neg, Wff.conj, Wff.biimp, Wff.ex",
        ]))
        attribute = "" if args_cli.explicit else "@[simp] "
        theorem = [
            f"{attribute}theorem fv_syn_{safe(rule.target_head)} {params} :",
            f"    (syn_{safe(rule.target_head)} {args}).fv = {lean(template)} := by",
            *facts,
            "  ext u",
            f"  simp [{simp_items}] <;> aesop",
        ]
        theorem_blocks.append("\n".join(theorem))
        map_lines.append(f"-- {rule.label} -> fv_syn_{safe(rule.target_head)}")

    header = f"""import CompactSourceSyntax

namespace NFChoice.Compiler.{module}

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

{"" if args_cli.explicit else "@[simp] "}theorem fv_syn_wtru : syn_wtru.fv = (∅ : Finset Var) := by
  rfl

"""
    footer = f"\n\nend NFChoice.Compiler.{module}\n"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(header + "\n\n".join(theorem_blocks) + footer, encoding="utf-8", newline="\n")
    manifest_output.write_text(json.dumps({
        "module": module,
        "global_simp_attributes": not args_cli.explicit,
        "definition_count": len(rules),
        "label_to_lemma": {
            rule.label: f"NFChoice.Compiler.{module}.fv_syn_{safe(rule.target_head)}"
            for rule in rules
        },
    }, indent=2) + "\n", encoding="utf-8", newline="\n")
    if args_cli.explicit:
        global_names = [
            "NFChoice.Compiler.CompactSyntaxFV.fv_syn_wtru",
            *(f"NFChoice.Compiler.CompactSyntaxFV.fv_syn_{safe(rule.target_head)}" for rule in rules),
        ]
        batches = [global_names[index:index + 12] for index in range(0, len(global_names), 12)]
        disable = (
            "import CompactSyntaxFV\n"
            "import CompactSyntaxFVExplicit\n\n"
            "/-! Disable the legacy global simp registration; use explicit FV lemmas. -/\n"
            + "\n".join("attribute [-simp] " + " ".join(batch) for batch in batches)
            + "\n"
        )
        (HERE / "generated/CompactSyntaxFVDisable.lean").write_text(
            disable, encoding="utf-8", newline="\n"
        )
    print(f"generated {len(rules)} FV theorems at {output}")


def walk_expr(expr: E):
    yield expr
    if expr[0] == "union":
        for item in expr[1]:
            yield from walk_expr(item)
    elif expr[0] == "erase":
        yield from walk_expr(expr[1])


def walk_ast(tree: AST):
    yield tree
    for argument in tree.args:
        yield from walk_ast(argument)


def vars_in_node(expr: E):
    if expr[0] == "singleton":
        return (expr[1],)
    if expr[0] == "erase":
        return (expr[2],)
    return ()


if __name__ == "__main__":
    main()
