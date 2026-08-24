#!/usr/bin/env python3
"""Emit the exact Metamath replay into Flypitch's syntactic proof type.

This is the proof-algebra variant of ``emit_full_compact_replay.py``.  The
source parser, theorem DAG, substitutions, and (crucially) every substituted
Metamath ``$d`` check are shared with the audited semantic emitter.  Only the
codomain changes from model validity to ``Nominal.NPrf``.

The emitter is deliberately fail-closed.  A primitive or definition which
does not yet have a syntactic handler aborts generation instead of becoming a
Lean axiom.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Mapping


HERE = Path(__file__).resolve().parent
COMPILER = HERE.parent / "compiler"
sys.path.insert(0, str(COMPILER))

import emit_full_compact_replay as base
from ast_replay import ASTReplayer, instantiate
from emit_source_native_smoke import safe, sha256
from mm_parser import Database, MMError, Statement
from syntax import AST, Grammar


OUT = HERE / "generated_nominal_replay_001"

NOMINAL_LITERAL_AXIOMS = frozenset(
    {
        "ax-ext", "ax-nin", "ax-sn", "ax-1c", "ax-xp", "ax-cnv",
        "ax-sset", "ax-si", "ax-ins2", "ax-ins3", "ax-typlower",
    }
)


class NominalEmitter(base.CompactEmitter):
    """The exact source replay with ``Nominal.NPrf`` as proof algebra."""

    def theorem_signature(self, statement: Statement) -> list[str]:
        params: list[str] = []
        for hyp in statement.hyps:
            if hyp.kind == "$f":
                sort, name = hyp.expr
                params.append(f"({safe(name)} : {self.sort_type(sort)})")
        for left, right in sorted(statement.dv):
            params.append(
                f"({self.dv_name(left, right)} : {self.dv_type(left, right)})"
            )
        for hyp in statement.hyps:
            if hyp.kind == "$e":
                params.append(
                    f"(hyp_{safe(hyp.label)} : Nominal.NPrf "
                    f"{self.expr(self.replayer.schema[hyp.label])})"
                )
        return params

    def logical_leaf(
        self, label: str, subst: Mapping[str, AST], essentials: list[str]
    ) -> str:
        a = {name: self.expr(tree) for name, tree in subst.items()}
        if label == "ax-mp":
            return f"Nominal.mp {essentials[0]} {essentials[1]}"
        if label == "ax-1":
            return f"Nominal.ax1 {a['ph']} {a['ps']}"
        if label == "ax-2":
            return f"Nominal.ax2 {a['ph']} {a['ps']} {a['ch']}"
        if label == "ax-3":
            return f"Nominal.ax3 {a['ph']} {a['ps']}"
        if label == "ax-gen":
            return f"Nominal.gen {essentials[0]} {a['x']}"
        if label == "ax-meredith":
            return (
                f"Nominal.axMeredith {a['ph']} {a['ps']} {a['ch']} "
                f"{a['th']} {a['ta']}"
            )
        if label == "ax-5":
            return f"Nominal.ax5 {a['x']} {a['ph']} {a['ps']}"
        if label == "ax-6":
            return f"Nominal.ax6 {a['x']} {a['ph']}"
        if label == "ax-7":
            return f"Nominal.ax7Structural {a['x']} {a['y']} {a['ph']}"
        if label == "ax-8":
            return f"Nominal.ax8 {a['x']} {a['y']} {a['z']}"
        if label == "ax-9":
            return f"Nominal.ax9 {a['x']} {a['y']}"
        if label == "ax-11":
            return f"Nominal.ax11Structural {a['x']} {a['y']} {a['ph']}"
        if label == "ax-12":
            return f"Nominal.ax12 {a['x']} {a['y']} {a['z']}"
        if label == "ax-13":
            return f"Nominal.ax13 {a['x']} {a['y']} {a['z']}"
        if label == "ax-14":
            return f"Nominal.ax14 {a['x']} {a['y']} {a['z']}"
        if label == "ax-17":
            return (
                f"Nominal.ax17 {a['ph']} {a['x']} "
                + self.dv_tactic(subst["x"], subst["ph"])
            )
        if label == "ax-ext":
            if essentials:
                raise MMError("unexpected essential hypotheses on ax-ext")
            return (
                "NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.axExt "
                f"{a['x']} {a['y']} {a['z']} "
                f"{self.dv_tactic(subst['x'], subst['y'])} "
                f"{self.dv_tactic(subst['x'], subst['z'])} "
                f"{self.dv_tactic(subst['y'], subst['z'])}"
            )
        if label == "ax-nin":
            if essentials:
                raise MMError("unexpected essential hypotheses on ax-nin")
            return (
                "NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.axNin "
                f"{a['x']} {a['y']} {a['z']} {a['w']} "
                f"{self.dv_tactic(subst['x'], subst['y'])} "
                f"{self.dv_tactic(subst['x'], subst['z'])} "
                f"{self.dv_tactic(subst['x'], subst['w'])} "
                f"{self.dv_tactic(subst['y'], subst['z'])} "
                f"{self.dv_tactic(subst['y'], subst['w'])} "
                f"{self.dv_tactic(subst['z'], subst['w'])}"
            )
        if label == "ax-sn":
            if essentials:
                raise MMError("unexpected essential hypotheses on ax-sn")
            return (
                "NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.axSn "
                f"{a['x']} {a['y']} {a['z']} "
                f"{self.dv_tactic(subst['x'], subst['y'])} "
                f"{self.dv_tactic(subst['x'], subst['z'])} "
                f"{self.dv_tactic(subst['y'], subst['z'])}"
            )
        if label == "ax-1c":
            if essentials:
                raise MMError("unexpected essential hypotheses on ax-1c")
            return (
                "NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.ax1c "
                f"{a['x']} {a['y']} {a['z']} {a['w']} "
                f"{self.dv_tactic(subst['x'], subst['y'])} "
                f"{self.dv_tactic(subst['x'], subst['z'])} "
                f"{self.dv_tactic(subst['x'], subst['w'])} "
                f"{self.dv_tactic(subst['y'], subst['z'])} "
                f"{self.dv_tactic(subst['y'], subst['w'])} "
                f"{self.dv_tactic(subst['z'], subst['w'])}"
            )
        if label == "ax-xp":
            if essentials:
                raise MMError("unexpected essential hypotheses on ax-xp")
            return (
                "NFChoice.DirectNominalPrf.Nominal."
                "NFLiteralXpViaCompletenessDev003.axXp "
                f"{a['x']} {a['y']} {a['z']} {a['w']} {a['t']} "
                f"{self.dv_tactic(subst['x'], subst['y'])} "
                f"{self.dv_tactic(subst['x'], subst['z'])} "
                f"{self.dv_tactic(subst['x'], subst['w'])} "
                f"{self.dv_tactic(subst['x'], subst['t'])} "
                f"{self.dv_tactic(subst['y'], subst['z'])} "
                f"{self.dv_tactic(subst['y'], subst['w'])} "
                f"{self.dv_tactic(subst['y'], subst['t'])} "
                f"{self.dv_tactic(subst['z'], subst['w'])} "
                f"{self.dv_tactic(subst['z'], subst['t'])} "
                f"{self.dv_tactic(subst['w'], subst['t'])}"
            )
        remaining_nf = {
            "ax-cnv": ("axCnv", ("x", "y", "z", "w")),
            "ax-sset": ("axSset", ("x", "y", "z", "w")),
            "ax-si": ("axSi", ("x", "y", "z", "w")),
            "ax-ins2": ("axIns2", ("x", "y", "z", "w", "t")),
            "ax-ins3": ("axIns3", ("x", "y", "z", "w", "t")),
            "ax-typlower": ("axTypeLower", ("x", "y", "z", "w")),
        }
        if label in remaining_nf:
            if essentials:
                raise MMError(
                    f"unexpected essential hypotheses on {label}"
                )
            theorem, names = remaining_nf[label]
            pieces = [
                "NFChoice.DirectNominalPrf.Nominal."
                "NFLiteralRemainingViaCompletenessDev001."
                + theorem
            ]
            pieces.extend(a[name] for name in names)
            pieces.extend(
                self.dv_tactic(subst[names[i]], subst[names[j]])
                for i in range(len(names))
                for j in range(i + 1, len(names))
            )
            return " ".join(pieces)
        # These handlers require structural lowering identities.  They are
        # intentionally named here only after the corresponding wrappers have
        # been checked; until then generation stops at the exact first use.
        raise MMError(f"UNSUPPORTED_NOMINAL_LOGICAL_LEAF {label}")

    def definition_leaf(
        self,
        label: str,
        subst: Mapping[str, AST],
        essentials: list[str],
        result: AST,
    ) -> str:
        entry = self.dispatch.get(label)
        if entry is None:
            raise MMError(f"definition has no audited dispatch: {label}")
        category = entry["category"]
        if label == "df-eu":
            if essentials:
                raise MMError("unexpected essential hypotheses on df-eu")
            a = {name: self.expr(tree) for name, tree in subst.items()}
            return (
                f"Nominal.dfEu {a['x']} {a['y']} {a['ph']} "
                f"{self.dv_tactic(subst['x'], subst['y'])} "
                f"{self.dv_tactic(subst['y'], subst['ph'])}"
            )
        if label == "df-nfc":
            if essentials:
                raise MMError("unexpected essential hypotheses on df-nfc")
            a = {name: self.expr(tree) for name, tree in subst.items()}
            return (
                "NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired."
                f"nominal_df_nfc {a['x']} {a['y']} {a['A']} "
                f"{self.dv_tactic(subst['A'], subst['y'])} "
                f"{self.dv_tactic(subst['x'], subst['y'])}"
            )
        if label == "df-clab":
            if essentials:
                raise MMError("unexpected essential hypotheses on df-clab")
            a = {name: self.expr(tree) for name, tree in subst.items()}
            return (
                "(by simpa ["
                "NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal, "
                "syn_wb, syn_wsb, syn_wa, syn_wex, "
                "Wff.biimp, Wff.ex, Wff.conj, Wff.neg, sbDefiniens] using "
                "(NFChoice.DirectNominalPrf.Nominal."
                "DefinitionLeafHandlersCanonical001.dfClabStructural "
                f"{a['x']} {a['y']} {a['ph']}))"
            )
        if label == "df-cleq":
            if len(essentials) != 1:
                raise MMError("df-cleq requires exactly its extensionality hypothesis")
            a = {name: self.expr(tree) for name, tree in subst.items()}
            return (
                "(by simpa ["
                "NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfCleqGoal, "
                "syn_wb, Wff.biimp, Wff.conj, Wff.neg] using "
                "(NFChoice.DirectNominalPrf.Nominal."
                "DefinitionLeafHandlersObjExtCompat001.dfCleqOfDVObjExt "
                f"{a['x']} {a['y']} {a['z']} {a['A']} {a['B']} "
                f"{essentials[0]} {self.dv_tactic(subst['x'], subst['A'])} "
                f"{self.dv_tactic(subst['x'], subst['B'])}))"
            )
        if label == "df-clel":
            if essentials:
                raise MMError("unexpected essential hypotheses on df-clel")
            a = {name: self.expr(tree) for name, tree in subst.items()}
            return (
                "(by simpa ["
                "NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, "
                "syn_wb, syn_wex, syn_wa, "
                "Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using "
                "(NFChoice.DirectNominalPrf.Nominal."
                "DefinitionLeafHandlersCanonical001.dfClelOfDV "
                f"{a['x']} {a['A']} {a['B']} "
                f"{self.dv_tactic(subst['x'], subst['A'])} "
                f"{self.dv_tactic(subst['x'], subst['B'])}))"
            )
        if label == "df-tru":
            if essentials:
                raise MMError("unexpected essential hypotheses on df-tru")
            dummy = self.expr(subst["ph"])
            return (
                "(by\n"
                "      have hTrue : Nominal.NPrf syn_wtru := by\n"
                "        simpa [syn_wtru] using (@g_id Wff.falsum)\n"
                f"      have hRhs : Nominal.NPrf (syn_wb {dummy} {dummy}) := "
                f"@g_biid {dummy}\n"
                f"      exact @g_impbii syn_wtru (syn_wb {dummy} {dummy})\n"
                f"        (Nominal.mp hRhs "
                f"(Nominal.ax1 (syn_wb {dummy} {dummy}) syn_wtru))\n"
                f"        (Nominal.mp hTrue "
                f"(Nominal.ax1 syn_wtru (syn_wb {dummy} {dummy}))))"
            )
        rule = self.rule_by_label.get(label)
        if rule is None:
            raise MMError(f"missing constructor rule for {label}")
        if essentials:
            raise MMError(f"unexpected essential hypotheses on {label}")
        lhs = instantiate(rule.lhs, subst)
        if category == "exact_biimp":
            unfolds: list[str] = []
            # A Metamath definition theorem is stated with the defined
            # biconditional connective ``wb`` at the outside.  Provenance in
            # the replay AST may expose its primitive ``wn`` expansion at
            # ``result.head``; use the source connective explicitly rather
            # than inventing the nonexistent primitive alias ``syn_wn``.
            for head in ("wb", rule.target_head):
                name = f"syn_{safe(head)}"
                if name not in unfolds:
                    unfolds.append(name)
            return (
                f"(by simpa [{', '.join(unfolds)}] using "
                f"(Nominal.biimpRefl {self.expr(lhs)}))"
            )
        if category == "exact_classEq":
            target = f"syn_{safe(rule.target_head)}"
            return (
                f"(by simpa [{target}] using "
                f"(Nominal.classEqRefl {self.expr(lhs)}))"
            )
        raise MMError(
            f"UNSUPPORTED_NOMINAL_DEFINITION {label} category={category}"
        )

    def leaf(
        self,
        label: str,
        subst: Mapping[str, AST],
        essentials: list[str],
        result: AST,
    ) -> str:
        if label in base.LOGICAL or label in NOMINAL_LITERAL_AXIOMS:
            return self.logical_leaf(label, subst, essentials)
        if label.startswith("df-"):
            return self.definition_leaf(label, subst, essentials, result)
        raise MMError(f"UNSUPPORTED_NOMINAL_LITERAL_LEAF {label}")

    def theorem_call(
        self, rule: Statement, subst: Mapping[str, AST], essentials: list[str]
    ) -> str:
        args = [f"@g_{safe(rule.label)}"]
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
        certificate = [
            line.replace(
                "RecanonWff.",
                "Nominal.RecanonTransportDev.TRecanonWff.",
            ).replace(
                "RecanonClass.",
                "Nominal.RecanonTransportDev.TRecanonClass.",
            )
            for line in certificate
        ]
        unfolds = self.recanon_unfolds(actual, expected)
        fv_lemmas: list[str] = []
        seen: set[str] = set()
        for tree in (actual, expected):
            for lemma in self.fv_lemmas(tree):
                if lemma not in seen:
                    seen.add(lemma)
                    fv_lemmas.append(lemma)
        lines = [
            f"  have {name} : Nominal.NPrf {self.expr(expected)} :=",
            "    Nominal.RecanonTransportDev.transport",
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
        text = super().emit_theorem(label, available)
        prefix = f"theorem g_{safe(label)}"
        if not text.startswith(prefix):
            raise MMError(f"unexpected inherited theorem header for {label}")
        text = "noncomputable def" + text[len("theorem") :]
        text = text.replace(
            f"Wff.Valid {base.SOURCE_MODEL} ", "Nominal.NPrf ", 1
        )
        if f"Wff.Valid {base.SOURCE_MODEL}" in text:
            raise MMError(f"semantic validity residue in {label}")
        return text


def proof_ops_digest(statement: Statement) -> str:
    return base.proof_ops_digest(statement)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--through", type=int, default=1)
    parser.add_argument("--start", type=int, default=1)
    args = parser.parse_args()
    sys.setrecursionlimit(200_000)

    database = Database()
    database.parse(base.SOURCE)
    grammar = Grammar(database)
    replayer = ASTReplayer(database, grammar)
    replayer.replay_closure("nchoice")
    emitter = NominalEmitter(database, replayer)

    metric_data = json.loads(base.METRICS.read_text(encoding="utf-8"))
    labels = [entry["label"] for entry in metric_data["theorems"]]
    chunks = metric_data["chunks"]
    if args.through < 1 or args.through > len(chunks):
        raise MMError(f"--through must be in 1..{len(chunks)}")
    if args.start < 1 or args.start > args.through:
        raise MMError("--start must be in 1..--through")

    OUT.mkdir(parents=True, exist_ok=True)
    cursor = 0
    available: set[str] = set()
    generated: list[dict[str, object]] = []
    for chunk in chunks[: args.through]:
        count = int(chunk["theorems"])
        chunk_labels = labels[cursor : cursor + count]
        cursor += count
        index = int(chunk["index"])
        if index < args.start:
            available.update(chunk_labels)
            continue
        before = len(emitter.trace)
        theorem_text: list[str] = []
        for label in chunk_labels:
            theorem_text.append(emitter.emit_theorem(label, frozenset(available)))
            available.add(label)

        module = f"NominalReplayChunk{index:03d}"
        imports = (
            "import CompactSourceSyntax\nimport NominalLoweringLemmas"
            if index == 1
            else f"import NominalReplayChunk{index - 1:03d}"
        )
        header = f"""{imports}

set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace NFChoice.DirectNominalPrf.Replay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax

"""
        footer = f"""

#print axioms g_{safe(chunk_labels[-1])}

end NFChoice.DirectNominalPrf.Replay
"""
        text = header + "\n\n".join(theorem_text) + footer
        output = OUT / f"{module}.lean"
        output.write_text(text, encoding="utf-8", newline="\n")
        trace = emitter.trace[before:]
        manifest = {
            "status": "GENERATED_UNCHECKED",
            "chunk": index,
            "source": str(base.SOURCE),
            "source_sha256": sha256(base.SOURCE.read_bytes()),
            "labels": chunk_labels,
            "theorem_count": len(chunk_labels),
            "proof_op_count": sum(
                len(database.statements[x].proof_ops) for x in chunk_labels
            ),
            "application_count": len(trace),
            "proof_ops_sha256": {
                x: proof_ops_digest(database.statements[x]) for x in chunk_labels
            },
            "output": str(output),
            "output_bytes": len(text.encode()),
            "output_sha256": sha256(text.encode()),
            "trace": trace,
        }
        manifest_path = OUT / f"nominal_replay_chunk_{index:03d}_manifest.json"
        manifest_path.write_text(
            json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n"
        )
        generated.append(
            {
                k: v
                for k, v in manifest.items()
                if k not in {"trace", "proof_ops_sha256"}
            }
        )
    print(json.dumps({"status": "GENERATED_UNCHECKED", "chunks": generated}, indent=2))


if __name__ == "__main__":
    main()
