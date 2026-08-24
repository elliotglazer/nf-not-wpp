#!/usr/bin/env python3
"""Emit the exact nchoice proof DAG in compact source syntax.

Every theorem interface is the raw Metamath AST translated homomorphically to
the audited ``syn_*`` constructors.  Lean infers intermediate result types;
the sidecar retains the exact source assertion, substitution, DV contract,
and proof ancestry for each semantic application.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Mapping

from ast_replay import ASTReplayer, instantiate
from definitions import DefinitionRule, Expander, ast_digest, extract_rules
from emit_source_native_smoke import SOURCE, StackEntry, safe, same_print, sha256
from mm_parser import Database, MMError, Statement
from syntax import AST, Grammar, erase_primitive_provenance

sys.path.insert(
    0, str(Path(__file__).resolve().parent.parent / "compact_replay_design/recanonicalization")
)
from emit_recanonicalization_smoke import CertificateEmitter as RecanonCertificateEmitter

sys.path.insert(
    0,
    str(
        Path(__file__).resolve().parent.parent
        / "df_leaf_semantics/symbolic_constructors"
    ),
)
from emit_compact_fv import EMPTY as FV_EMPTY
from emit_compact_fv import FV as SymbolicFV


HERE = Path(__file__).resolve().parent
OUT = HERE / "full_compact_replay_001" / "generated"
METRICS = HERE / "generated" / "full_symbolic_replay_metrics.json"
DISPATCH = (
    HERE.parent
    / "df_leaf_semantics/df_dispatch/alpha_transport/definition_dispatch_map_v2.json"
)
EXACT_DF_CALLS = (
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_exact_001/compact_df_exact_manifest.json"
)
ALPHA_CALL_MANIFESTS = (
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_chunk001_001/CompactDFAlpha001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_iun_001/CompactDFAlphaUrgent002.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_1c_001/CompactDFAlphaUrgent003.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_xpk_001/CompactDFAlphaUrgent004.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_cnvk_001/CompactDFAlphaUrgent005.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_ins2k_001/CompactDFAlphaUrgent006.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_ins3k_001/CompactDFAlphaUrgent007.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_imak_001/CompactDFAlphaUrgent008.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_p6_001/CompactDFAlphaUrgent009.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_sik_001/CompactDFAlphaUrgent010.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_ssetk_001/CompactDFAlphaUrgent011.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_idk_001/CompactDFAlphaUrgent012.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_iota_001/CompactDFAlphaUrgent013.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_addc_001/CompactDFAlphaUrgent014.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_nnc_001/CompactDFAlphaUrgent015.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_lefin_001/CompactDFAlphaUrgent016.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_ltfin_001/CompactDFAlphaUrgent017.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_ncfin_001/CompactDFAlphaUrgent018.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_tfin_001/CompactDFAlphaUrgent019.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_evenfin_001/CompactDFAlphaUrgent020.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_oddfin_001/CompactDFAlphaUrgent021.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_sfin_001/CompactDFAlphaUrgent022.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_spfin_001/CompactDFAlphaUrgent023.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_phi_001/CompactDFAlphaUrgent024.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_op_focused_001/CompactDFAlphaOpFocusedProbe005.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_proj1_001/CompactDFAlphaUrgent026.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_proj2_001/CompactDFAlphaUrgent027.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_opab_001/CompactDFAlphaUrgent028.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_1st_focused_structural_001/CompactDFAlpha1stFocusedProd001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_swap_focused_split_001/CompactDFAlphaSwapFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_sset_focused_split_001/CompactDFAlphaSsetFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/audit_alpha_ima_focused_split_001/CompactDFAlphaImaFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaCoFocusedSplit003.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaSiFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaXpFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlpha2ndFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaIdFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaCnvFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaFvFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaOprabFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaMptFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaMpt2FocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaCupFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaComposeFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaDisjFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaAddcfnFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaUrgent047.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaFnsFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaPw1fnFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaClos1FocusedSplit002.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaTransFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaFoundFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaSymFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaRefFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaAntisymFocusedSplit001.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaUrgent056.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaUrgent057.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaUrgent058.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaUrgent059.json",
    HERE.parent
    / "df_leaf_semantics/compact_df_wrappers/generated/CompactDFAlphaUrgent060.json",
    HERE.parent
    / "replay_provenance_audit/alpha_suffix_queue_u056_u064_002/generated/CompactDFAlphaUrgent061.json",
    HERE.parent
    / "replay_provenance_audit/alpha_suffix_queue_u056_u064_002/generated/CompactDFAlphaUrgent062.json",
    HERE.parent
    / "replay_provenance_audit/alpha_suffix_queue_u056_u064_002/generated/CompactDFAlphaUrgent063.json",
    HERE.parent
    / "replay_provenance_audit/alpha_suffix_queue_u056_u064_002/generated/CompactDFAlphaUrgent064.json",
)

LOGICAL = frozenset(
    {
        "ax-mp", "ax-1", "ax-2", "ax-3", "ax-gen", "ax-5", "ax-6",
        "ax-7", "ax-8", "ax-9", "ax-11", "ax-12", "ax-13", "ax-14",
        "ax-17", "ax-meredith",
    }
)

# Metamath uses ``S`` as a class metavariable in later theorems.  Keep the
# ambient Flypitch structure in a name outside the source variable alphabet.
SOURCE_MODEL = "_model"

# Until the audited all-constructor FV module lands, these early source heads
# are enough for chunks 1--4.  Later chunks import its compact simp theorems.
EARLY_DV_SIMPS = (
    "syn_wb", "syn_wo", "syn_wa", "syn_w3o", "syn_w3a", "syn_wnan",
    "syn_wtru", "syn_wex", "syn_wnf", "syn_wsb",
)


class ProvenanceBlindExpander(Expander):
    """Choose the same hidden dummy for primitive/generic printed aliases."""

    @staticmethod
    def _fresh_dummy(rule: DefinitionRule, sort: str, name: str, actual: AST) -> AST:
        digest = ast_digest(erase_primitive_provenance(actual))[:16]
        clean_label = rule.label.replace("-", "_")
        return AST.variable(sort, f"__{clean_label}_{name}_{digest}")


class CompactEmitter:
    def __init__(self, database: Database, replayer: ASTReplayer) -> None:
        self.database = database
        self.replayer = replayer
        self.rules = extract_rules(database, replayer)
        self.rule_by_label: dict[str, DefinitionRule] = {
            rule.label: rule for rule in self.rules
        }
        self.rule_by_head: dict[tuple[str, str], DefinitionRule] = {
            (rule.target_sort, rule.target_head): rule for rule in self.rules
        }
        self.defined_heads = {
            (rule.target_sort, rule.target_head) for rule in self.rules
        }
        self.recanon_expander = ProvenanceBlindExpander(self.rules)
        self.recanon_certificate = RecanonCertificateEmitter()
        dispatch_data = json.loads(DISPATCH.read_text(encoding="utf-8"))
        self.dispatch = {entry["label"]: entry for entry in dispatch_data["entries"]}
        exact_df_data = json.loads(EXACT_DF_CALLS.read_text(encoding="utf-8"))
        self.exact_df_calls = {entry["label"]: entry for entry in exact_df_data["calls"]}
        for alpha_manifest in ALPHA_CALL_MANIFESTS:
            alpha_data = json.loads(alpha_manifest.read_text(encoding="utf-8"))
            self.exact_df_calls.update(
                {entry["label"]: entry for entry in alpha_data["records"]}
            )
        self.trace: list[dict[str, object]] = []
        # Optional proof-shaping mode used by bounded append-only refinements.
        # When a theorem label is selected, every substituted source-DV proof
        # is declared immediately after the fresh-variable prelude.  Calls then
        # reference those names, so late elaboration never scans hundreds of
        # large Valid proof locals.  The Metamath application DAG is unchanged.
        self.cache_dv_labels: set[str] = set()
        self._dv_cache: dict[str, tuple[str, str]] | None = None
        self._current_theorem: Statement | None = None
        self._current_local_sorts: dict[str, str] = {}

        # Reuse the exact symbolic-support algebra which generated the audited
        # CompactSyntaxFVExplicit equations.  Keeping the templates here lets
        # cached DV proofs follow those equations structurally, instead of
        # asking simp/aesop to search a large proof context.
        self.symbolic_fv = SymbolicFV(self.rules)
        for rule in self.rules:
            dummy_names = {name for _sort, name in rule.dummy_variables}
            template = self.symbolic_fv.of(rule.rhs, dummy_names)
            self.symbolic_fv.templates[rule.target_head] = template

    def expr(self, tree: AST) -> str:
        if tree.is_variable:
            return safe(tree.variable_name)
        args = [self.expr(arg) for arg in tree.args]
        if tree.sort == "class":
            if tree.head == "cv" and len(args) == 1:
                return f"(.cv {args[0]})"
            if tree.head == "cab" and len(args) == 2:
                return f"(.cab {args[0]} {args[1]})"
            if (tree.sort, tree.head) in self.defined_heads:
                return f"(syn_{safe(tree.head)} {' '.join(args)})" if args else f"(syn_{safe(tree.head)})"
            raise MMError(f"unsupported raw class head: {tree.sexpr()}")
        if tree.sort != "wff":
            raise MMError(f"cannot emit sort {tree.sort}: {tree.sexpr()}")
        if tree.head == "wbot" and not args:
            return ".falsum"
        if tree.head == "wtru" and not args:
            return "syn_wtru"
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
        if (tree.sort, tree.head) in self.defined_heads:
            return f"(syn_{safe(tree.head)} {' '.join(args)})" if args else f"(syn_{safe(tree.head)})"
        raise MMError(f"unsupported raw wff head: {tree.sexpr()}")

    def normalize_recanon(self, tree: AST) -> AST:
        if tree.sort == "wff":
            return self.recanon_expander.expand_wff(tree)
        if tree.sort == "class":
            return self.recanon_expander.expand_class(tree)
        return tree

    def recanon_unfolds(self, *trees: AST) -> tuple[str, ...]:
        """Definitions which Lean must delta-reduce for a core certificate."""
        result: list[str] = []
        seen: set[tuple[str, str]] = set()

        def visit(node: AST) -> None:
            if node.is_variable:
                return
            key = (node.sort, node.head)
            if node.head == "wtru":
                if key not in seen:
                    seen.add(key)
                    result.append("syn_wtru")
                return
            rule = self.rule_by_head.get(key)
            if rule is not None:
                if key in seen:
                    return
                seen.add(key)
                result.append(f"syn_{safe(node.head)}")
                visit(rule.rhs)
                for argument in node.args:
                    visit(argument)
                return
            for argument in node.args:
                visit(argument)

        for tree in trees:
            visit(tree)
        return tuple(result)

    @staticmethod
    def sort_type(sort: str) -> str:
        return {"setvar": "Var", "wff": "Wff", "class": "Class"}[sort]

    @staticmethod
    def support_expr(name: str, sort: str) -> str:
        ident = safe(name)
        if sort == "setvar":
            return f"({{{ident}}} : Finset Var)"
        return f"{ident}.fv"

    def dv_type(self, left: str, right: str) -> str:
        ls = self.database.variable_type[left]
        rs = self.database.variable_type[right]
        li, ri = safe(left), safe(right)
        if ls == "setvar" and rs == "setvar":
            return f"{li} ≠ {ri}"
        if ls == "setvar":
            return f"{li} ∉ {self.support_expr(right, rs)}"
        if rs == "setvar":
            return f"{ri} ∉ {self.support_expr(left, ls)}"
        return f"Disjoint {self.support_expr(left, ls)} {self.support_expr(right, rs)}"

    @staticmethod
    def dv_name(left: str, right: str) -> str:
        return f"dv_{safe(left)}_{safe(right)}"

    def theorem_signature(self, statement: Statement) -> list[str]:
        params = [
            f"{{{SOURCE_MODEL} : Fol.Structure LNF}}",
            f"(hNF : Fol.all_realize_sentence {SOURCE_MODEL} LiteralHailperinNF)",
        ]
        for hyp in statement.hyps:
            if hyp.kind == "$f":
                sort, name = hyp.expr
                params.append(f"({safe(name)} : {self.sort_type(sort)})")
        for left, right in sorted(statement.dv):
            params.append(f"({self.dv_name(left, right)} : {self.dv_type(left, right)})")
        for hyp in statement.hyps:
            if hyp.kind == "$e":
                params.append(
                    f"(hyp_{safe(hyp.label)} : Wff.Valid {SOURCE_MODEL} {self.expr(self.replayer.schema[hyp.label])})"
                )
        return params

    def local_variables(self, theorem: Statement) -> list[tuple[str, str]]:
        mandatory = {hyp.expr[1] for hyp in theorem.hyps if hyp.kind == "$f"}
        seen: set[str] = set()
        result: list[tuple[str, str]] = []
        for op in theorem.proof_ops:
            if op.kind != "label":
                continue
            rule = self.database.statements[str(op.value)]
            if rule.kind != "$f":
                continue
            sort, name = rule.expr
            if name in mandatory or name in seen:
                continue
            seen.add(name)
            result.append((sort, name))
        return result

    def support_expression(self, theorem: Statement) -> str:
        terms = [
            self.support_expr(h.expr[1], h.expr[0])
            for h in theorem.hyps if h.kind == "$f"
        ]
        return " ∪ ".join(terms) if terms else "(∅ : Finset Var)"

    def local_prelude(self, theorem: Statement) -> list[str]:
        lines = [f"  let proofSupport : Finset Var := {self.support_expression(theorem)}"]
        formal_hyps = [hyp for hyp in theorem.hyps if hyp.kind == "$f"]

        def support_member(index: int, base: str) -> str:
            """Embed membership in one support summand into the left-associated union."""
            proof = base
            if index > 0:
                proof = f"Finset.mem_union_right _ ({proof})"
            for _ in range(index + 1, len(formal_hyps)):
                proof = f"Finset.mem_union_left _ ({proof})"
            return proof

        fresh: list[tuple[str, int]] = []
        offset = 0
        for sort, name in self.local_variables(theorem):
            ident = safe(name)
            if sort == "setvar":
                lines.append(f"  let {ident} : Var := freshVar proofSupport {offset}")
                fresh.append((ident, offset))
                offset += 1
            elif sort == "wff":
                lines.append(f"  let {ident} : Wff := .falsum")
            elif sort == "class":
                binder = f"proofBinder_{ident}"
                lines.append(f"  let {binder} : Var := freshVar proofSupport {offset}")
                lines.append(f"  let {ident} : Class := .cab {binder} .falsum")
                fresh.append((binder, offset))
                offset += 1
            else:
                raise MMError(f"unsupported local sort {sort} in {theorem.label}")
        for ident, index in fresh:
            lines += [
                f"  have fresh_{ident} : {ident} ∉ proofSupport := by",
                f"    change freshVar proofSupport {index} ∉ proofSupport",
                f"    exact freshVar_not_mem proofSupport {index}",
            ]
            for formal_index, hyp in enumerate(formal_hyps):
                sort, name = hyp.expr
                formal = safe(name)
                if sort == "setvar":
                    member = support_member(
                        formal_index, "Finset.mem_singleton.mpr h"
                    )
                    lines += [
                        f"  have fresh_{ident}_ne_{formal} : {ident} ≠ {formal} := by",
                        "    intro h",
                        f"    exact fresh_{ident} ({member})",
                        f"  have fresh_{formal}_ne_{ident} : {formal} ≠ {ident} :=",
                        f"    Ne.symm fresh_{ident}_ne_{formal}",
                    ]
                elif sort in {"wff", "class"}:
                    member = support_member(formal_index, "h")
                    lines += [
                        f"  have fresh_{ident}_not_{formal} : {ident} ∉ {formal}.fv := by",
                        "    intro h",
                        f"    exact fresh_{ident} ({member})",
                    ]
        for i, (left, li) in enumerate(fresh):
            for right, ri in fresh[i + 1:]:
                lines += [
                    f"  have fresh_{left}_ne_{right} : {left} ≠ {right} := by",
                    f"    change freshVar proofSupport {li} ≠ freshVar proofSupport {ri}",
                    f"    exact freshVar_injective proofSupport (i := {li}) (j := {ri}) (by decide)",
                    f"  have fresh_{right}_ne_{left} : {right} ≠ {left} :=",
                    f"    Ne.symm fresh_{left}_ne_{right}",
                ]
        return lines

    def fv_lemmas(self, tree: AST) -> tuple[str, ...]:
        """Exact, non-global FV rewrite lemmas needed by one substituted DV."""
        result: list[str] = []
        seen: set[str] = set()

        def add(name: str) -> None:
            if name not in seen:
                seen.add(name)
                result.append(name)

        core = {
            ("class", "cv"): "fv_class_cv",
            ("class", "cab"): "fv_class_cab",
            ("wff", "wbot"): "fv_wff_falsum",
            ("wff", "wn"): "fv_wff_neg",
            ("wff", "wi"): "fv_wff_imp",
            ("wff", "wal"): "fv_wff_all",
            ("wff", "weq"): "fv_wff_objEq",
            ("wff", "wel"): "fv_wff_objMem",
            ("wff", "wceq"): "fv_wff_classEq",
            ("wff", "wcel"): "fv_wff_classMem",
        }

        def visit(node: AST) -> None:
            if node.is_variable or node.sort == "setvar":
                return
            if (node.sort, node.head) in self.defined_heads or node.head == "wtru":
                add(
                    "NFChoice.Compiler.CompactSyntaxFVExplicit."
                    f"fv_syn_{safe(node.head)}"
                )
            else:
                lemma = core.get((node.sort, node.head))
                if lemma is not None:
                    add(f"NFChoice.Compiler.CoreFVSimp.{lemma}")
            for argument in node.args:
                visit(argument)

        visit(tree)
        return tuple(result)

    def qualified_expr(self, tree: AST) -> str:
        """Emit an AST where a root dotted constructor has an explicit sort."""
        expression = self.expr(tree)
        if expression.startswith("(."):
            prefix = "Wff" if tree.sort == "wff" else "Class"
            return f"({prefix}.{expression[2:]}"
        if expression == ".falsum":
            return "Wff.falsum"
        return expression

    def substituted_dv_type(self, left: AST, right: AST) -> str:
        left_expr = self.qualified_expr(left)
        right_expr = self.qualified_expr(right)
        if left.sort == "setvar" and right.sort == "setvar":
            return f"{left_expr} ≠ {right_expr}"
        if left.sort == "setvar":
            return f"{left_expr} ∉ ({right_expr}).fv"
        if right.sort == "setvar":
            return f"{right_expr} ∉ ({left_expr}).fv"
        return f"Disjoint ({left_expr}).fv ({right_expr}).fv"

    def _source_dv_fact(self, left: str, right: str) -> tuple[str, bool] | None:
        """Return a mandatory source-DV fact and whether it needs symmetry."""

        theorem = self._current_theorem
        if theorem is None:
            raise MMError("source DV lookup outside theorem emission")
        for source_left, source_right in theorem.dv:
            if source_left == left and source_right == right:
                return self.dv_name(source_left, source_right), False
            if source_left == right and source_right == left:
                return self.dv_name(source_left, source_right), True
        return None

    def _setvar_inequality_term(self, left: AST, right: AST) -> str:
        if not (left.is_variable and right.is_variable):
            raise MMError("non-variable setvar in structural DV certificate")
        left_name = safe(left.variable_name)
        right_name = safe(right.variable_name)
        target = f"{left_name} ≠ {right_name}"
        if left_name == right_name:
            raise MMError(f"impossible strict DV {left_name} != {right_name}")
        left_local = left.variable_name in self._current_local_sorts
        right_local = right.variable_name in self._current_local_sorts
        if left_local or right_local:
            candidate = f"fresh_{left_name}_ne_{right_name}"
            return f"(show {target} from (by exact {candidate}))"
        source = self._source_dv_fact(left.variable_name, right.variable_name)
        if source is None:
            return f"(show {target} from (by assumption))"
        fact, reverse = source
        return (
            f"(show {target} from "
            f"(by exact {'Ne.symm ' if reverse else ''}{fact}))"
        )

    def _atomic_not_mem_term(self, variable: AST, tree: AST) -> str:
        if not (variable.is_variable and variable.sort == "setvar"):
            raise MMError("bad setvar in atomic FV certificate")
        if not (tree.is_variable and tree.sort in {"wff", "class"}):
            raise MMError("bad support atom in structural FV certificate")
        variable_name = safe(variable.variable_name)
        tree_name = safe(tree.variable_name)
        target = f"{variable_name} ∉ ({tree_name}).fv"
        if tree.variable_name in self._current_local_sorts:
            # Proof-local wffs/classes are definitionally empty-support values.
            return f"(show {target} from (by simp [{tree_name}, Wff.fv, Class.fv]))"
        if variable.variable_name in self._current_local_sorts:
            return f"(show {target} from (by exact fresh_{variable_name}_not_{tree_name}))"
        source = self._source_dv_fact(variable.variable_name, tree.variable_name)
        if source is None:
            return f"(show {target} from (by assumption))"
        fact, _reverse = source
        # A setvar/non-setvar DV has the same normalized Lean proposition in
        # either source pair order, so no symmetry transport is needed.
        return f"(show {target} from (by exact {fact}))"

    def _actualize_fv_template(
        self, template: tuple, rule: DefinitionRule, actual: AST
    ) -> tuple:
        supports: dict[str, AST] = {}
        variables: dict[str, AST] = {}
        for formal, argument in zip(rule.lhs.args, actual.args):
            if formal.sort == "setvar":
                variables[formal.variable_name] = argument
            else:
                supports[formal.variable_name] = argument

        def visit(expr: tuple) -> tuple:
            tag = expr[0]
            if tag == "empty":
                return expr
            if tag == "atom":
                return ("tree", supports[expr[1]])
            if tag == "singleton":
                return ("singleton_tree", variables[expr[1].name])
            if tag == "union":
                return ("union", tuple(visit(item) for item in expr[1]))
            if tag == "erase":
                return ("erase_tree", visit(expr[1]), variables[expr[2].name])
            raise MMError(f"unsupported FV template tag {tag}")

        return visit(template)

    def _head_fv_support(self, tree: AST) -> tuple[str, tuple]:
        """Return the audited root FV equation and its immediate RHS shape."""

        if tree.is_variable:
            raise MMError("variable has no root FV equation")
        if (tree.sort, tree.head) in self.defined_heads:
            rule = self.rule_by_head[(tree.sort, tree.head)]
            template = self.symbolic_fv.templates[tree.head]
            return (
                "NFChoice.Compiler.CompactSyntaxFVExplicit."
                f"fv_syn_{safe(tree.head)}",
                self._actualize_fv_template(template, rule, tree),
            )
        if tree.head == "wtru":
            return (
                "NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru",
                FV_EMPTY,
            )
        core_prefix = "NFChoice.Compiler.CoreFVSimp."
        if tree.head == "cv":
            return core_prefix + "fv_class_cv", ("singleton_tree", tree.args[0])
        if tree.head == "cab":
            return core_prefix + "fv_class_cab", (
                "erase_tree", ("tree", tree.args[1]), tree.args[0]
            )
        if tree.head == "wbot":
            return core_prefix + "fv_wff_falsum", FV_EMPTY
        if tree.head == "wn":
            return core_prefix + "fv_wff_neg", ("tree", tree.args[0])
        if tree.head == "wi":
            return core_prefix + "fv_wff_imp", (
                "union", tuple(("tree", arg) for arg in tree.args)
            )
        if tree.head == "wal":
            return core_prefix + "fv_wff_all", (
                "erase_tree", ("tree", tree.args[1]), tree.args[0]
            )
        if tree.head in {"weq", "wel"}:
            suffix = "objEq" if tree.head == "weq" else "objMem"
            return core_prefix + f"fv_wff_{suffix}", (
                "pair_tree", tree.args[0], tree.args[1]
            )
        if tree.head in {"wceq", "wcel"}:
            suffix = "classEq" if tree.head == "wceq" else "classMem"
            return core_prefix + f"fv_wff_{suffix}", (
                "union", tuple(("tree", arg) for arg in tree.args)
            )
        raise MMError(f"missing root FV equation for {tree.sexpr()}")

    def _fv_support_expr(self, support: tuple) -> str:
        tag = support[0]
        if tag == "empty":
            return "(∅ : Finset Var)"
        if tag == "tree":
            return f"({self.qualified_expr(support[1])}).fv"
        if tag == "singleton_tree":
            return f"({{{self.qualified_expr(support[1])}}} : Finset Var)"
        if tag == "pair_tree":
            left = self.qualified_expr(support[1])
            right = self.qualified_expr(support[2])
            return f"({{{left}, {right}}} : Finset Var)"
        if tag == "union":
            items = support[1]
            if not items:
                return "(∅ : Finset Var)"
            return " ∪ ".join(f"({self._fv_support_expr(item)})" for item in items)
        if tag == "erase_tree":
            inner = self._fv_support_expr(support[1])
            binder = self.qualified_expr(support[2])
            return f"({inner}).erase {binder}"
        raise MMError(f"unsupported actual FV support tag {tag}")

    def _not_mem_support_term(self, variable: AST, support: tuple) -> str:
        tag = support[0]
        variable_expr = self.qualified_expr(variable)
        support_expr = self._fv_support_expr(support)
        if tag == "empty":
            raw = "(fun hmem => by cases hmem)"
            return f"(show {variable_expr} ∉ {support_expr} from {raw})"
        if tag == "tree":
            return self._not_mem_tree_term(variable, support[1])
        if tag == "singleton_tree":
            inequality = self._setvar_inequality_term(variable, support[1])
            raw = (
                "(by simpa only [Finset.mem_singleton] using "
                f"{inequality})"
            )
            return f"(show {variable_expr} ∉ {support_expr} from {raw})"
        if tag == "pair_tree":
            left = self._setvar_inequality_term(variable, support[1])
            right = self._setvar_inequality_term(variable, support[2])
            raw = (
                "(by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; "
                f"exact ⟨{left}, {right}⟩)"
            )
            return f"(show {variable_expr} ∉ {support_expr} from {raw})"
        if tag == "union":
            items = support[1]
            if not items:
                raw = "(fun hmem => by cases hmem)"
                return f"(show {variable_expr} ∉ {support_expr} from {raw})"
            result = self._not_mem_support_term(variable, items[0])
            for item in items[1:]:
                right = self._not_mem_support_term(variable, item)
                result = (
                    "(fun hmem => (Finset.mem_union.mp hmem).elim "
                    f"{result} {right})"
                )
            return f"(show {variable_expr} ∉ {support_expr} from {result})"
        if tag == "erase_tree":
            inner, binder = support[1], support[2]
            if variable == binder:
                raw = "(by simp only [Finset.mem_erase])"
            else:
                inner_term = self._not_mem_support_term(variable, inner)
                raw = (
                    "(fun hmem => "
                    f"{inner_term} (Finset.mem_of_mem_erase hmem))"
                )
            return f"(show {variable_expr} ∉ {support_expr} from {raw})"
        raise MMError(f"unsupported actual FV support tag {tag}")

    def _not_mem_tree_term(self, variable: AST, tree: AST) -> str:
        if tree.is_variable:
            return self._atomic_not_mem_term(variable, tree)
        lemma, support = self._head_fv_support(tree)
        proof = self._not_mem_support_term(variable, support)
        target = (
            f"{self.qualified_expr(variable)} ∉ "
            f"({self.qualified_expr(tree)}).fv"
        )
        return f"(show {target} from (by rw [{lemma}]; exact {proof}))"

    def structural_dv_tactic(self, left: AST, right: AST) -> str | None:
        if left.sort == "setvar" and right.sort == "setvar":
            return self._setvar_inequality_term(left, right)
        if left.sort == "setvar":
            return f"(by exact {self._not_mem_tree_term(left, right)})"
        if right.sort == "setvar":
            return f"(by exact {self._not_mem_tree_term(right, left)})"
        return None

    def dv_tactic(self, *trees: AST) -> str:
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
            "(by first | "
            "(simp (config := { failIfUnchanged := false }) "
            f"only [{simp_set}] at ⊢ <;> aesop) | assumption)"
        )
        if self._dv_cache is not None and len(trees) == 2:
            structural = self.structural_dv_tactic(trees[0], trees[1])
            if structural is not None:
                tactic = structural
        if self._dv_cache is None:
            return tactic
        if len(trees) != 2:
            raise MMError(f"cached DV expected two trees, got {len(trees)}")
        target = self.substituted_dv_type(trees[0], trees[1])
        cached = self._dv_cache.get(target)
        if cached is None:
            name = f"dv_cache_{len(self._dv_cache) + 1:04d}"
            self._dv_cache[target] = (name, tactic)
        else:
            name = cached[0]
        return name

    def logical_leaf(self, label: str, subst: Mapping[str, AST], essentials: list[str]) -> str:
        a = {name: self.expr(tree) for name, tree in subst.items()}
        if label == "ax-mp":
            return f"Wff.valid_mp {essentials[0]} {essentials[1]}"
        if label == "ax-1":
            return f"NFChoice.LogicalSemantics.Wff.valid_ax_1 (S := {SOURCE_MODEL}) {a['ph']} {a['ps']}"
        if label == "ax-2":
            return f"NFChoice.LogicalSemantics.Wff.valid_ax_2 (S := {SOURCE_MODEL}) {a['ph']} {a['ps']} {a['ch']}"
        if label == "ax-3":
            return f"NFChoice.LogicalSemantics.Wff.valid_ax_3 (S := {SOURCE_MODEL}) {a['ph']} {a['ps']}"
        if label == "ax-gen":
            return f"Wff.valid_generalization {essentials[0]} {a['x']}"
        mapping = {
            "ax-5": ("valid_ax_5", ("x", "ph", "ps")),
            "ax-6": ("valid_ax_6", ("x", "ph")),
            "ax-7": ("valid_ax_7", ("x", "y", "ph")),
            "ax-8": ("valid_ax_8", ("x", "y", "z")),
            "ax-9": ("valid_ax_9", ("x", "y")),
            "ax-11": ("valid_ax_11", ("x", "y", "ph")),
            "ax-12": ("valid_ax_12", ("x", "y", "z")),
            "ax-13": ("valid_ax_13", ("x", "y", "z")),
            "ax-14": ("valid_ax_14", ("x", "y", "z")),
            "ax-meredith": ("valid_ax_meredith", ("ph", "ps", "ch", "th", "ta")),
        }
        if label in mapping:
            lemma, order = mapping[label]
            return "NFChoice.LogicalSemantics.Wff." + lemma + f" (S := {SOURCE_MODEL}) " + " ".join(a[x] for x in order)
        if label == "ax-17":
            return (
                f"NFChoice.LogicalSemantics.Wff.valid_ax_17 (S := {SOURCE_MODEL}) {a['x']} {a['ph']} "
                + self.dv_tactic(subst["x"], subst["ph"])
            )
        raise MMError(f"unsupported logical leaf {label}")

    def definition_leaf(
        self, label: str, subst: Mapping[str, AST], essentials: list[str], result: AST
    ) -> str:
        entry = self.dispatch.get(label)
        if entry is None:
            raise MMError(f"definition has no audited dispatch: {label}")
        category = entry["category"]
        call = self.exact_df_calls.get(label)
        if call is not None:
            args = [call["theorem"], f"(S := {SOURCE_MODEL})", "hNF"]
            args.extend(self.expr(subst[name]) for name in call["floating"])
            args.extend(
                self.dv_tactic(subst[left], subst[right])
                for left, right in call["dv"]
            )
            if len(essentials) != len(call["essential"]):
                raise MMError(
                    f"definition essential arity mismatch {label}: "
                    f"{len(essentials)} != {len(call['essential'])}"
                )
            args.extend(essentials)
            return " ".join(args)
        rule = self.rule_by_label.get(label)
        if rule is None:
            raise MMError(f"missing constructor rule for {label}")
        target = f"syn_{safe(rule.target_head)}"
        lhs = instantiate(rule.lhs, subst)
        if category == "exact_biimp":
            return (
                f"(by simpa [{target}] using "
                f"(NFChoice.DefinitionLeaves.Wff.valid_biimp_refl (S := {SOURCE_MODEL}) {self.expr(lhs)}))"
            )
        if category == "exact_classEq":
            return (
                f"(by simpa [{target}] using "
                f"(NFChoice.DefinitionLeaves.Class.valid_classEq_refl (S := {SOURCE_MODEL}) {self.expr(lhs)}))"
            )
        raise MMError(f"UNSUPPORTED_DEFINITION {label} category={category}")

    def leaf(self, label: str, subst: Mapping[str, AST], essentials: list[str], result: AST) -> str:
        if label in LOGICAL:
            return self.logical_leaf(label, subst, essentials)
        if label.startswith("df-"):
            return self.definition_leaf(label, subst, essentials, result)
        if label == "ax-ext":
            return (
                f"NFChoice.Compiler.SourceNativeGate.source_ax_ext (S := {SOURCE_MODEL}) hNF "
                f"{self.expr(subst['x'])} {self.expr(subst['y'])} {self.expr(subst['z'])} "
                f"{self.dv_tactic(subst['x'], subst['y'])} "
                f"{self.dv_tactic(subst['x'], subst['z'])} "
                f"{self.dv_tactic(subst['y'], subst['z'])}"
            )
        if label in {"ax-nin", "ax-sn", "ax-1c"}:
            theorem = {
                "ax-nin": "axNinCompact",
                "ax-sn": "axSnCompact",
                "ax-1c": "ax1cCompact",
            }[label]
            variables = {
                "ax-nin": ("x", "y", "z", "w"),
                "ax-sn": ("x", "y", "z"),
                "ax-1c": ("x", "y", "z", "w"),
            }[label]
            dv_pairs = {
                "ax-nin": (("x", "y"), ("x", "z"), ("x", "w"),
                           ("y", "z"), ("y", "w"), ("z", "w")),
                "ax-sn": (("x", "y"), ("x", "z"), ("y", "z")),
                "ax-1c": (("x", "y"), ("x", "z"), ("x", "w"),
                          ("y", "z"), ("y", "w"), ("z", "w")),
            }[label]
            args = [
                f"NFChoice.Compiler.NFCompactLeafGate.{theorem}",
                f"(S := {SOURCE_MODEL})",
                "hNF",
            ]
            args.extend(self.expr(subst[name]) for name in variables)
            args.extend(self.dv_tactic(subst[x], subst[y]) for x, y in dv_pairs)
            return " ".join(args)
        final_nf_leaves = {
            "ax-xp": ("axXpCompact", ("x", "y", "z", "w", "t")),
            "ax-cnv": ("axCnvCompact", ("x", "y", "z", "w")),
            "ax-sset": ("axSsetCompact", ("x", "y", "z", "w")),
            "ax-si": ("axSiCompact", ("x", "y", "z", "w")),
            "ax-ins2": ("axIns2Compact", ("x", "y", "z", "w", "t")),
            "ax-ins3": ("axIns3Compact", ("x", "y", "z", "w", "t")),
            "ax-typlower": ("axTypeLowerCompact", ("x", "y", "z", "w")),
        }
        if label in final_nf_leaves:
            theorem, variables = final_nf_leaves[label]
            args = [
                f"NFChoice.Compiler.NFCompactLeafFinalGate.{theorem}",
                f"(S := {SOURCE_MODEL})",
                "hNF",
            ]
            args.extend(self.expr(subst[name]) for name in variables)
            args.extend(
                self.dv_tactic(subst[variables[i]], subst[variables[j]])
                for i in range(len(variables))
                for j in range(i + 1, len(variables))
            )
            return " ".join(args)
        raise MMError(f"UNSUPPORTED_LITERAL_LEAF {label}")

    def theorem_call(self, rule: Statement, subst: Mapping[str, AST], essentials: list[str]) -> str:
        # Positional explicit application remains stable across the legacy
        # chunks (whose ambient-structure binder was named ``S``) and the
        # collision-safe chunks (whose binder is named ``_model``).
        args = [f"@g_{safe(rule.label)} {SOURCE_MODEL} hNF"]
        for hyp in rule.hyps:
            if hyp.kind == "$f":
                args.append(self.expr(subst[hyp.expr[1]]))
        for left, right in sorted(rule.dv):
            args.append(self.dv_tactic(subst[left], subst[right]))
        args.extend(essentials)
        return " ".join(args)

    def emit_recanon_bridge(
        self, name: str, actual: AST, expected: AST, source_proof: str
    ) -> list[str]:
        left = self.normalize_recanon(actual)
        right = self.normalize_recanon(expected)
        certificate = self.recanon_certificate.wff(left, right, "        ")
        unfolds = self.recanon_unfolds(actual, expected)
        fv_lemmas: list[str] = []
        seen: set[str] = set()
        for tree in (actual, expected):
            for lemma in self.fv_lemmas(tree):
                if lemma not in seen:
                    seen.add(lemma)
                    fv_lemmas.append(lemma)
        lines = [
            f"  have {name} : Wff.Valid {SOURCE_MODEL} {self.expr(expected)} :=",
            "    RecanonWff.valid_mpr (extensional_of_literal_model hNF)",
            "      (by",
        ]
        if unfolds:
            lines.append("        unfold " + " ".join(unfolds))
        if fv_lemmas:
            lines.append(
                "        simp (config := { failIfUnchanged := false }) only ["
                + ", ".join(fv_lemmas)
                + "]"
            )
        lines.extend(certificate)
        lines += ["      )", f"      {source_proof}"]
        return lines

    def emit_theorem(self, label: str, available: frozenset[str]) -> str:
        theorem = self.database.statements[label]
        if self._current_theorem is not None:
            raise MMError("nested theorem emission")
        self._current_theorem = theorem
        self._current_local_sorts = {
            name: sort for sort, name in self.local_variables(theorem)
        }
        params = self.theorem_signature(theorem)
        conclusion = self.replayer.schema[label]
        header = [
            f"theorem g_{safe(label)}",
            "    " + " ".join(params) + " :",
            f"    Wff.Valid {SOURCE_MODEL} {self.expr(conclusion)} := by",
        ]
        prelude = self.local_prelude(theorem)
        lines = [*header, *prelude]
        cache_enabled = label in self.cache_dv_labels
        if self._dv_cache is not None:
            raise MMError("nested DV cache activation")
        if cache_enabled:
            self._dv_cache = {}
        stack: list[StackEntry] = []
        saved: list[StackEntry] = []
        proof_index = 0
        for op_index, op in enumerate(theorem.proof_ops):
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
                stack.append(StackEntry(self.replayer.schema[reference], f"hyp_{safe(reference)}"))
                continue
            arity = len(rule.hyps)
            arguments = stack[-arity:] if arity else []
            if arity:
                del stack[-arity:]
            subst: dict[str, AST] = {}
            essential_proofs: list[str] = []
            essential_records: list[dict[str, object]] = []
            for hyp, actual in zip(rule.hyps, arguments):
                if hyp.kind == "$f":
                    subst[hyp.expr[1]] = actual.ast
                    continue
                if actual.proof is None:
                    raise MMError(f"missing essential proof at {reference} in {label}")
                expected = instantiate(self.replayer.schema[hyp.label], subst)
                if expected != actual.ast:
                    if same_print(expected, actual.ast):
                        bridge = (
                            f"p{proof_index:04d}_e{len(essential_records):02d}_recanon"
                        )
                        lines.extend(
                            self.emit_recanon_bridge(
                                bridge, actual.ast, expected, actual.proof
                            )
                        )
                        essential_proofs.append(bridge)
                        essential_records.append(
                            {
                                "hyp": hyp.label,
                                "proof": bridge,
                                "source_proof": actual.proof,
                                "recanonicalized": True,
                                "bridge_node": bridge,
                                "actual_ast_sha256": ast_digest(actual.ast).upper(),
                                "expected_ast_sha256": ast_digest(expected).upper(),
                            }
                        )
                        continue
                    raise MMError(f"essential mismatch at {reference} in {label}")
                essential_proofs.append(actual.proof)
                essential_records.append(
                    {
                        "hyp": hyp.label,
                        "proof": actual.proof,
                        "source_proof": actual.proof,
                        "recanonicalized": False,
                        "bridge_node": None,
                        "actual_ast_sha256": ast_digest(actual.ast).upper(),
                        "expected_ast_sha256": ast_digest(expected).upper(),
                    }
                )
            result = instantiate(self.replayer.schema[reference], subst)
            if rule.typecode != "|-":
                stack.append(StackEntry(result, None))
                continue
            if rule.kind == "$a":
                proof = self.leaf(reference, subst, essential_proofs, result)
            else:
                if reference not in available:
                    raise MMError(f"unavailable theorem {reference} in {label}")
                proof = self.theorem_call(rule, subst, essential_proofs)
            node = f"p{proof_index:04d}"
            proof_index += 1
            lines += [f"  have {node} :=", f"    {proof}"]
            self.trace.append(
                {
                    "theorem": label,
                    "proof_op_index": op_index,
                    "node": node,
                    "source_assertion": reference,
                    "source_assertion_kind": rule.kind,
                    "result_ast_sha256": ast_digest(result).upper(),
                    "substitution": {k: ast_digest(v).upper() for k, v in sorted(subst.items())},
                    "source_dv": [list(pair) for pair in sorted(rule.dv)],
                    "essential_inputs": essential_records,
                }
            )
            stack.append(StackEntry(result, node))
        if len(stack) != 1 or stack[0].proof is None:
            raise MMError(f"bad final stack for {label}")
        if stack[0].ast != conclusion:
            raise MMError(f"raw conclusion mismatch for {label}")
        lines.append(f"  exact {stack[0].proof}")
        if cache_enabled:
            assert self._dv_cache is not None
            declarations: list[str] = []
            prior_cache_names: list[str] = []
            for target, (name, tactic) in self._dv_cache.items():
                declarations.append(f"  have {name} : {target} := by")
                if prior_cache_names:
                    # A cached proof was valid before any cache facts existed.
                    # Hide earlier cache locals so aesop/simp sees the same
                    # bounded source/freshness context at every declaration.
                    declarations.append(
                        "    clear " + " ".join(prior_cache_names)
                    )
                declarations.append(f"    exact {tactic}")
                prior_cache_names.append(name)
            insertion = len(header) + len(prelude)
            lines[insertion:insertion] = declarations
            self._dv_cache = None
        self._current_theorem = None
        self._current_local_sorts = {}
        return "\n".join(lines)


def proof_ops_digest(statement: Statement) -> str:
    payload = "\n".join(f"{op.kind}:{op.value}" for op in statement.proof_ops).encode()
    return sha256(payload)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--through", type=int, default=1)
    parser.add_argument("--start", type=int, default=1)
    parser.add_argument(
        "--scan-missing",
        action="store_true",
        help="report every unsupported semantic leaf in the selected chunks without emitting",
    )
    args = parser.parse_args()
    sys.setrecursionlimit(200_000)

    database = Database()
    database.parse(SOURCE)
    grammar = Grammar(database)
    replayer = ASTReplayer(database, grammar)
    replayer.replay_closure("nchoice")
    emitter = CompactEmitter(database, replayer)

    metric_data = json.loads(METRICS.read_text(encoding="utf-8"))
    labels = [entry["label"] for entry in metric_data["theorems"]]
    chunks = metric_data["chunks"]
    if args.through < 1 or args.through > len(chunks):
        raise MMError(f"--through must be in 1..{len(chunks)}")
    if args.start < 1 or args.start > args.through:
        raise MMError("--start must be in 1..--through")

    if args.scan_missing:
        supported_literal = LOGICAL | frozenset(
            {
                "ax-ext", "ax-nin", "ax-sn", "ax-1c", "ax-xp", "ax-cnv",
                "ax-sset", "ax-si", "ax-ins2", "ax-ins3", "ax-typlower",
            }
        )
        missing: list[dict[str, object]] = []
        seen_missing: set[str] = set()
        cursor = 0
        for chunk in chunks[:args.through]:
            chunk_labels = labels[cursor:cursor + int(chunk["theorems"])]
            cursor += len(chunk_labels)
            index = int(chunk["index"])
            if index < args.start:
                continue
            for theorem_label in chunk_labels:
                for op in database.statements[theorem_label].proof_ops:
                    if op.kind != "label":
                        continue
                    reference = str(op.value)
                    rule = database.statements[reference]
                    if rule.kind != "$a" or rule.typecode != "|-":
                        continue
                    category = emitter.dispatch.get(reference, {}).get("category")
                    unsupported = (
                        reference.startswith("df-")
                        and isinstance(category, str)
                        and category.startswith("alpha")
                        and reference not in emitter.exact_df_calls
                    ) or (
                        not reference.startswith("df-")
                        and reference not in supported_literal
                    )
                    if unsupported and reference not in seen_missing:
                        seen_missing.add(reference)
                        missing.append(
                            {
                                "chunk": index,
                                "theorem": theorem_label,
                                "label": reference,
                                "category": category or "literal",
                            }
                        )
        print(json.dumps({"status": "SCAN", "missing": missing}, indent=2))
        return

    OUT.mkdir(parents=True, exist_ok=True)
    cursor = 0
    available: set[str] = set()
    generated: list[dict[str, object]] = []
    for chunk in chunks[:args.through]:
        chunk_labels = labels[cursor:cursor + int(chunk["theorems"])]
        cursor += len(chunk_labels)
        index = int(chunk["index"])
        if index < args.start:
            available.update(chunk_labels)
            continue
        before = len(emitter.trace)
        theorem_text: list[str] = []
        for label in chunk_labels:
            theorem_text.append(emitter.emit_theorem(label, frozenset(available)))
            available.add(label)
        module = f"FullCompactReplayChunk{index:03d}"
        if index == 1:
            imports = "\n".join(
                [
                    "import CompactSourceSyntax",
                    "import LogicalSemantics.Basic",
                    "import ReplaySupport.Basic",
                    "import DefinitionLeaves.Basic",
                ]
            )
        else:
            previous = f"FullCompactReplayChunk{index - 1:03d}"
            if index >= 9:
                previous += "Split"
            imports = f"import {previous}"
            if index >= 4:
                imports += (
                    "\nimport CompactSyntaxFV\nimport CoreFVSimp\nimport CompactDFExact"
                    "\nimport CompactDFAlpha001\nimport CompactDFAlphaUrgent002"
                    "\nimport CompactDFAlphaUrgent003"
                    "\nimport CompactDFAlphaUrgent004"
                    "\nimport CompactDFAlphaUrgent005"
                    "\nimport CompactDFAlphaUrgent006"
                    "\nimport CompactDFAlphaUrgent007"
                    "\nimport CompactDFAlphaUrgent008"
                    "\nimport CompactDFAlphaUrgent009"
                    "\nimport CompactDFAlphaUrgent010"
                    "\nimport CompactDFAlphaUrgent011"
                    "\nimport CompactDFAlphaUrgent012"
                    "\nimport CompactDFAlphaUrgent013"
                    "\nimport CompactDFAlphaUrgent014"
                    "\nimport CompactDFAlphaUrgent015"
                    "\nimport CompactDFAlphaUrgent016"
                    "\nimport CompactDFAlphaUrgent017"
                    "\nimport CompactDFAlphaUrgent018"
                    "\nimport CompactDFAlphaUrgent019"
                    "\nimport CompactDFAlphaUrgent020"
                    "\nimport CompactDFAlphaUrgent021"
                    "\nimport CompactDFAlphaUrgent022"
                    "\nimport CompactDFAlphaUrgent023"
                    "\nimport CompactDFAlphaUrgent024"
                    "\nimport CompactDFAlphaOpFocusedProbe005"
                    "\nimport CompactDFAlphaUrgent026"
                    "\nimport CompactDFAlphaUrgent027"
                    "\nimport CompactDFAlphaUrgent028"
                    "\nimport CompactDFAlpha1stFocusedProd001"
                    "\nimport CompactDFAlphaSwapFocusedSplit001"
                    "\nimport CompactDFAlphaSsetFocusedSplit001"
                    "\nimport CompactDFAlphaImaFocusedSplit001"
                    "\nimport CompactDFAlphaCoTopLift002"
                    "\nimport CompactDFAlphaSiTopLift002"
                    "\nimport CompactDFAlphaXpFocusedSplit001TopLift"
                    "\nimport CompactDFAlpha2ndTopLift002"
                    "\nimport CompactDFAlphaIdTopLift002"
                    "\nimport CompactDFAlphaCnvTopLift002"
                    "\nimport CompactDFAlphaFvTopLift002"
                    "\nimport CompactDFAlphaOprabFocusedSplit001BranchLift"
                    "\nimport CompactDFAlphaMptFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaMpt2FocusedSplit001BranchLift"
                    "\nimport CompactDFAlphaCupFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaComposeFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaDisjFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaAddcfnFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaUrgent047TopV2"
                    "\nimport CompactDFAlphaFnsFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaPw1fnFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaClos1FocusedSplit002TopLift"
                    "\nimport CompactDFAlphaTransFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaFoundFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaSymFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaRefFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaAntisymFocusedSplit001TopLift"
                    "\nimport CompactDFAlphaUrgent056TopLift"
                    "\nimport CompactDFAlphaUrgent057TopLift"
                    "\nimport CompactDFAlphaUrgent058TopLift"
                    "\nimport CompactDFAlphaUrgent059TopLift"
                    "\nimport CompactDFAlphaUrgent060TopLift"
                    "\nimport CompactDFAlphaUrgent061TopLift"
                    "\nimport CompactDFAlphaUrgent062TopLift"
                    "\nimport CompactDFAlphaUrgent063TopLiftB50S150"
                    "\nimport CompactDFAlphaUrgent064TopLiftB50S150"
                    "\nimport Recanonicalization"
                    "\nimport SourceNativeGate"
                    "\nimport NFCompactLeafGate"
                    "\nimport NFCompactLeafFinalGate"
                    "\nimport CompactSyntaxFVDisable"
                )
        header = f"""{imports}

set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NFChoice.Compiler.FullCompactReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.CompactReplayDesign.Recanonicalization

"""
        footer = f"""

#print axioms g_{safe(chunk_labels[-1])}

end NFChoice.Compiler.FullCompactReplay
"""
        text = header + "\n\n".join(theorem_text) + footer
        output = OUT / f"{module}.lean"
        output.write_text(text, encoding="utf-8", newline="\n")
        trace = emitter.trace[before:]
        manifest = {
            "status": "GENERATED_UNCHECKED",
            "chunk": index,
            "source": str(SOURCE),
            "source_sha256": sha256(SOURCE.read_bytes()),
            "labels": chunk_labels,
            "theorem_count": len(chunk_labels),
            "proof_op_count": sum(len(database.statements[x].proof_ops) for x in chunk_labels),
            "semantic_application_count": len(trace),
            "proof_ops_sha256": {x: proof_ops_digest(database.statements[x]) for x in chunk_labels},
            "output": str(output),
            "output_bytes": len(text.encode()),
            "output_sha256": sha256(text.encode()),
            "trace": trace,
        }
        manifest_path = OUT / f"full_compact_replay_chunk_{index:03d}_manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n")
        generated.append({k: v for k, v in manifest.items() if k != "trace" and k != "proof_ops_sha256"})
    print(json.dumps({"status": "GENERATED_UNCHECKED", "chunks": generated}, indent=2))


if __name__ == "__main__":
    main()
