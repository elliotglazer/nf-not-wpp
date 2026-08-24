#!/usr/bin/env python3
"""Emit the WPP-only extension of the compact nominal semantic replay.

The generator reuses a Choice theorem only through the frozen 2,925-entry
fingerprint manifest.  All other semantic theorems are regenerated from the
repaired WPP source's decoded Metamath proof program.  WPP-specific alpha
definition calls are accepted only from explicit machine manifests.

This script deliberately refuses to emit a theorem with 10,000 or more proof
operations until an intra-theorem top-level-lift plan exists for that theorem.
The guard prevents an accidental monolithic kernel run on the very large WPP
proofs.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Mapping

from wpp_config import (
    CHOICE_COMPILER,
    CHOICE_REUSE_MODULE,
    CHOICE_REUSE_NAMESPACE,
    ENDPOINT,
    METRICS,
    MISSING_LEAVES,
    REPLAY_OUT,
    REUSE_MANIFEST,
    WPP_FV_MODULE,
    WPP_SOURCE,
    WPP_SOURCE_SHA256,
    WPP_SYNTAX_MODULE,
    sha256_bytes,
    sha256_file,
    verify_pinned_inputs,
    verify_surface_inputs,
)

sys.path.insert(0, str(CHOICE_COMPILER))
import emit_full_compact_replay as choice_replay  # noqa: E402
from ast_replay import ASTReplayer  # noqa: E402
from definitions import DefinitionRule, extract_rules  # noqa: E402
from mm_parser import Database, MMError, Statement  # noqa: E402
from syntax import AST, Grammar  # noqa: E402


HERE = Path(__file__).resolve().parent
MISSING_AUDIT = HERE / "audits/missing_leaves_002/resource.json"
INTRA_THEOREM_LIFT_PROOF_OPS = 10_000


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2) + "\n").encode()


def write_exact(path: Path, data: bytes) -> None:
    if path.exists():
        if path.read_bytes() != data:
            raise RuntimeError(f"append-only output differs: {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def load_call_manifest(path: Path) -> tuple[str | None, list[dict[str, object]]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    source_sha = data.get("source_sha256")
    if source_sha is not None and source_sha != WPP_SOURCE_SHA256:
        raise MMError(f"WPP leaf manifest source mismatch: {path}")
    records = data.get("records", data.get("calls", data.get("entries")))
    if not isinstance(records, list):
        raise MMError(f"leaf manifest has no records/calls/entries array: {path}")
    module = data.get("module")
    return (str(module) if module else None, records)


def definition_category(rule: DefinitionRule, replayer: ASTReplayer) -> str:
    schema = replayer.schema[rule.label]
    if schema.head == "wb":
        suffix = "biimp"
    elif schema.head == "wceq":
        suffix = "classEq"
    else:
        raise MMError(f"unexpected definition schema at {rule.label}: {schema.sexpr()}")
    return ("alpha_" if rule.dummy_variables else "exact_") + suffix


class WPPCompactEmitter(choice_replay.CompactEmitter):
    def __init__(
        self,
        database: Database,
        replayer: ASTReplayer,
        reused_entries: Mapping[str, dict[str, object]],
        leaf_manifests: tuple[Path, ...],
    ) -> None:
        # This mirrors the final Choice emitter constructor, but extracts rules
        # from the explicitly named WPP endpoint instead of its old default.
        self.database = database
        self.replayer = replayer
        self.rules = extract_rules(database, replayer, ENDPOINT)
        self.rule_by_label = {rule.label: rule for rule in self.rules}
        self.rule_by_head = {
            (rule.target_sort, rule.target_head): rule for rule in self.rules
        }
        self.defined_heads = {
            (rule.target_sort, rule.target_head) for rule in self.rules
        }
        self.recanon_expander = choice_replay.ProvenanceBlindExpander(self.rules)
        self.recanon_certificate = choice_replay.RecanonCertificateEmitter()

        old_dispatch = json.loads(choice_replay.DISPATCH.read_text(encoding="utf-8"))
        self.dispatch = {entry["label"]: entry for entry in old_dispatch["entries"]}
        for rule in self.rules:
            if rule.label not in self.dispatch:
                self.dispatch[rule.label] = {
                    "label": rule.label,
                    "category": definition_category(rule, replayer),
                    "target_head": rule.target_head,
                    "dummy_count": len(rule.dummy_variables),
                }

        old_exact = json.loads(choice_replay.EXACT_DF_CALLS.read_text(encoding="utf-8"))
        self.exact_df_calls = {entry["label"]: entry for entry in old_exact["calls"]}
        for old_alpha in choice_replay.ALPHA_CALL_MANIFESTS:
            data = json.loads(old_alpha.read_text(encoding="utf-8"))
            self.exact_df_calls.update(
                {entry["label"]: entry for entry in data["records"]}
            )
        self.wpp_leaf_modules: list[str] = []
        self.wpp_leaf_manifests: list[dict[str, str]] = []
        for path in leaf_manifests:
            module, records = load_call_manifest(path)
            for entry in records:
                label = str(entry["label"])
                if label in self.exact_df_calls:
                    raise MMError(f"duplicate definition call record {label}: {path}")
                self.exact_df_calls[label] = entry
            if module and module not in self.wpp_leaf_modules:
                self.wpp_leaf_modules.append(module)
            self.wpp_leaf_manifests.append(
                {"path": str(path), "sha256": sha256_file(path)}
            )

        self.reused_entries = dict(reused_entries)
        self.trace: list[dict[str, object]] = []
        self.cache_dv_labels: set[str] = set()
        self._dv_cache: dict[str, tuple[str, str]] | None = None
        self._current_theorem: Statement | None = None
        self._current_local_sorts: dict[str, str] = {}
        self.symbolic_fv = choice_replay.SymbolicFV(self.rules)
        for rule in self.rules:
            dummy_names = {name for _sort, name in rule.dummy_variables}
            template = self.symbolic_fv.of(rule.rhs, dummy_names)
            self.symbolic_fv.templates[rule.target_head] = template

    def theorem_call(
        self, rule: Statement, subst: Mapping[str, AST], essentials: list[str]
    ) -> str:
        if rule.label in self.reused_entries:
            theorem = f"{CHOICE_REUSE_NAMESPACE}.g_{choice_replay.safe(rule.label)}"
        else:
            theorem = f"g_{choice_replay.safe(rule.label)}"
        args = [f"@{theorem} {choice_replay.SOURCE_MODEL} hNF"]
        for hyp in rule.hyps:
            if hyp.kind == "$f":
                args.append(self.expr(subst[hyp.expr[1]]))
        for left, right in sorted(rule.dv):
            args.append(self.dv_tactic(subst[left], subst[right]))
        args.extend(essentials)
        return " ".join(args)

    def emit_theorem(self, label: str, available: frozenset[str]) -> str:
        before = len(self.trace)
        text = super().emit_theorem(label, available)
        for record in self.trace[before:]:
            reference = str(record["source_assertion"])
            reused = self.reused_entries.get(reference)
            if reused is not None:
                record["theorem_origin"] = "choice_exact_reuse"
                record["reuse_interface_sha256"] = reused["interface_sha256"]
                record["reuse_proof_ops_sha256"] = reused["proof_ops_sha256"]
                record["reuse_choice_chunk"] = reused["choice_chunk"]
            elif record["source_assertion_kind"] == "$p":
                record["theorem_origin"] = "wpp_regenerated"
            else:
                record["theorem_origin"] = "semantic_leaf"
        return text


def load_frontend(
    leaf_manifests: tuple[Path, ...],
) -> tuple[
    Database,
    ASTReplayer,
    WPPCompactEmitter,
    dict[str, object],
    dict[str, object],
]:
    verify_pinned_inputs()
    verify_surface_inputs()
    reuse = json.loads(REUSE_MANIFEST.read_text(encoding="utf-8"))
    metrics = json.loads(METRICS.read_text(encoding="utf-8"))
    if reuse.get("status") != "PASS" or metrics.get("status") != "MEASURED":
        raise MMError("reuse/metrics prerequisite is not frozen PASS")
    if reuse["wpp_source"]["sha256"] != WPP_SOURCE_SHA256:
        raise MMError("reuse source mismatch")
    if metrics["reuse_manifest_sha256"] != sha256_file(REUSE_MANIFEST):
        raise MMError("metrics/reuse manifest mismatch")
    entries = {str(entry["label"]): entry for entry in reuse["entries"]}
    if len(entries) != 2925:
        raise MMError("reuse manifest does not contain 2925 unique labels")
    database = Database()
    database.parse(WPP_SOURCE)
    replayer = ASTReplayer(database, Grammar(database))
    audit = replayer.replay_closure(ENDPOINT)
    if audit.endpoint_ast.sexpr() != "(wn wwpp)":
        raise MMError(f"unexpected WPP endpoint AST {audit.endpoint_ast.sexpr()}")
    emitter = WPPCompactEmitter(database, replayer, entries, leaf_manifests)
    return database, replayer, emitter, reuse, metrics


def selected_labels(metrics: dict[str, object]) -> tuple[list[str], list[dict[str, object]]]:
    theorem_metrics = metrics["theorems"]
    chunks = metrics["chunks"]
    if not isinstance(theorem_metrics, list) or not isinstance(chunks, list):
        raise MMError("bad metrics theorem/chunk arrays")
    return [str(entry["label"]) for entry in theorem_metrics], chunks


def scan_missing(
    database: Database,
    emitter: WPPCompactEmitter,
    metrics: dict[str, object],
) -> dict[str, object]:
    labels, chunks = selected_labels(metrics)
    literal_supported = choice_replay.LOGICAL | frozenset(
        {
            "ax-ext",
            "ax-nin",
            "ax-sn",
            "ax-1c",
            "ax-xp",
            "ax-cnv",
            "ax-sset",
            "ax-si",
            "ax-ins2",
            "ax-ins3",
            "ax-typlower",
        }
    )
    missing_by_label: dict[str, dict[str, object]] = {}
    exact_inline: set[str] = set()
    used_leaves: set[str] = set()
    cursor = 0
    for chunk in chunks:
        count = int(chunk["theorems"])
        chunk_labels = labels[cursor : cursor + count]
        cursor += count
        chunk_index = int(chunk["index"])
        for theorem_label in chunk_labels:
            for op in database.statements[theorem_label].proof_ops:
                if op.kind != "label":
                    continue
                reference = str(op.value)
                statement = database.statements[reference]
                if statement.kind != "$a" or statement.typecode != "|-":
                    continue
                used_leaves.add(reference)
                if reference.startswith("df-"):
                    entry = emitter.dispatch.get(reference)
                    if entry is None:
                        category = "unknown_definition"
                    else:
                        category = str(entry["category"])
                    if reference not in emitter.exact_df_calls:
                        if category.startswith("alpha") or category in {
                            "unknown_definition",
                            "semantic_boundary",
                            "special_semantic_lemma",
                        }:
                            current = missing_by_label.get(reference)
                            if current is None:
                                rule = emitter.rule_by_label.get(reference)
                                current = {
                                    "label": reference,
                                    "category": category,
                                    "first_chunk": chunk_index,
                                    "first_theorem": theorem_label,
                                    "occurrences": 0,
                                    "target_head": rule.target_head if rule else None,
                                    "dummy_count": len(rule.dummy_variables) if rule else None,
                                }
                                missing_by_label[reference] = current
                            current["occurrences"] = int(current["occurrences"]) + 1
                        else:
                            exact_inline.add(reference)
                elif reference not in literal_supported:
                    current = missing_by_label.get(reference)
                    if current is None:
                        current = {
                            "label": reference,
                            "category": "literal",
                            "first_chunk": chunk_index,
                            "first_theorem": theorem_label,
                            "occurrences": 0,
                        }
                        missing_by_label[reference] = current
                    current["occurrences"] = int(current["occurrences"]) + 1
    if cursor != len(labels):
        raise MMError(f"chunk coverage mismatch: {cursor} != {len(labels)}")
    missing = list(missing_by_label.values())
    return {
        "schema": "nf-wpp-missing-leaf-scan-v1",
        "status": "SCAN",
        "source": str(WPP_SOURCE),
        "source_sha256": WPP_SOURCE_SHA256,
        "endpoint": ENDPOINT,
        "reuse_manifest": str(REUSE_MANIFEST),
        "reuse_manifest_sha256": sha256_file(REUSE_MANIFEST),
        "metrics": str(METRICS),
        "metrics_sha256": sha256_file(METRICS),
        "surface_modules": [WPP_SYNTAX_MODULE, WPP_FV_MODULE],
        "leaf_manifests": emitter.wpp_leaf_manifests,
        "counts": {
            "wpp_only_theorems_scanned": len(labels),
            "used_formula_leaves": len(used_leaves),
            "missing_unique": len(missing),
            "missing_alpha_definitions": sum(
                1 for item in missing if str(item["category"]).startswith("alpha")
            ),
            "missing_literals": sum(1 for item in missing if item["category"] == "literal"),
            "exact_definitions_supported_inline": len(exact_inline),
        },
        "exact_definitions_supported_inline": sorted(exact_inline),
        "missing": missing,
    }


def emit_chunks(
    database: Database,
    emitter: WPPCompactEmitter,
    reuse: dict[str, object],
    metrics: dict[str, object],
    start: int,
    through: int,
) -> list[dict[str, object]]:
    labels, chunks = selected_labels(metrics)
    if start < 1 or through < start or through > len(chunks):
        raise MMError(f"chunk range must satisfy 1 <= start <= through <= {len(chunks)}")
    scan = scan_missing(database, emitter, metrics)
    if scan["missing"]:
        labels_missing = ", ".join(item["label"] for item in scan["missing"][:12])
        raise MMError(
            f"cannot emit with {scan['counts']['missing_unique']} missing leaves: "
            f"{labels_missing}"
        )

    reused = {str(entry["label"]) for entry in reuse["entries"]}
    available = set(reused)
    cursor = 0
    generated: list[dict[str, object]] = []
    REPLAY_OUT.mkdir(parents=True, exist_ok=True)
    for chunk in chunks:
        count = int(chunk["theorems"])
        chunk_labels = labels[cursor : cursor + count]
        cursor += count
        index = int(chunk["index"])
        if index < start:
            available.update(chunk_labels)
            continue
        if index > through:
            break
        oversized = [
            label
            for label in chunk_labels
            if len(database.statements[label].proof_ops) >= INTRA_THEOREM_LIFT_PROOF_OPS
        ]
        if oversized:
            raise MMError(
                f"chunk {index} requires intra-theorem lift before source emission: "
                + ", ".join(oversized)
            )
        before = len(emitter.trace)
        theorem_texts: list[str] = []
        for label in chunk_labels:
            theorem_texts.append(emitter.emit_theorem(label, frozenset(available)))
            available.add(label)
        module = f"FullWPPCompactReplayChunk{index:03d}"
        if index == 1:
            imports = [
                f"import {CHOICE_REUSE_MODULE}",
                f"import {WPP_SYNTAX_MODULE}",
                f"import {WPP_FV_MODULE}",
                *(f"import {name}" for name in emitter.wpp_leaf_modules),
            ]
        else:
            imports = [f"import FullWPPCompactReplayChunk{index - 1:03d}"]
        header = "\n".join(imports) + """

set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NFChoice.Compiler.FullWPPCompactReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.CompactReplayDesign.Recanonicalization

"""
        footer = (
            f"\n\n#print axioms g_{choice_replay.safe(chunk_labels[-1])}\n\n"
            "end NFChoice.Compiler.FullWPPCompactReplay\n"
        )
        text = header + "\n\n".join(theorem_texts) + footer
        output = REPLAY_OUT / f"{module}.lean"
        output_bytes = text.encode()
        write_exact(output, output_bytes)
        trace = emitter.trace[before:]
        manifest = {
            "schema": "nf-wpp-compact-replay-chunk-v1",
            "status": "GENERATED_UNCHECKED",
            "chunk": index,
            "source": str(WPP_SOURCE),
            "source_sha256": WPP_SOURCE_SHA256,
            "endpoint": ENDPOINT,
            "reuse_manifest": str(REUSE_MANIFEST),
            "reuse_manifest_sha256": sha256_file(REUSE_MANIFEST),
            "leaf_manifests": emitter.wpp_leaf_manifests,
            "labels": chunk_labels,
            "theorem_count": len(chunk_labels),
            "proof_op_count": sum(
                len(database.statements[label].proof_ops) for label in chunk_labels
            ),
            "semantic_application_count": len(trace),
            "proof_ops_sha256": {
                label: choice_replay.proof_ops_digest(database.statements[label])
                for label in chunk_labels
            },
            "output": str(output),
            "output_bytes": len(output_bytes),
            "output_sha256": sha256_bytes(output_bytes),
            "trace": trace,
        }
        manifest_path = REPLAY_OUT / f"wpp_compact_replay_chunk_{index:03d}_manifest.json"
        manifest_bytes = json_bytes(manifest)
        write_exact(manifest_path, manifest_bytes)
        generated.append(
            {
                key: value
                for key, value in manifest.items()
                if key not in {"trace", "proof_ops_sha256"}
            }
        )
    return generated


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--leaf-manifest", action="append", default=[])
    parser.add_argument("--scan-missing", action="store_true")
    parser.add_argument("--scan-output", type=Path, default=MISSING_LEAVES)
    parser.add_argument("--start", type=int, default=1)
    parser.add_argument("--through", type=int, default=1)
    args = parser.parse_args()
    sys.setrecursionlimit(200_000)
    leaf_manifests = tuple(Path(path).resolve() for path in args.leaf_manifest)
    database, _replayer, emitter, reuse, metrics = load_frontend(leaf_manifests)
    if args.scan_missing:
        record = scan_missing(database, emitter, metrics)
        data = json_bytes(record)
        write_exact(args.scan_output, data)
        if args.scan_output.resolve() == MISSING_LEAVES.resolve() and not leaf_manifests:
            resource = {
                "schema": "nf-wpp-missing-leaf-audit-v1",
                "status": "PASS",
                "builder": str(Path(__file__)),
                "builder_sha256": sha256_file(Path(__file__)),
                "scan": str(args.scan_output),
                "scan_sha256": sha256_bytes(data),
                "source_sha256": WPP_SOURCE_SHA256,
                "endpoint": ENDPOINT,
                "counts": record["counts"],
                "kernel_compile_started": False,
            }
            resource_data = json_bytes(resource)
            write_exact(MISSING_AUDIT, resource_data)
            record["audit"] = {
                "path": str(MISSING_AUDIT),
                "sha256": sha256_bytes(resource_data),
            }
        print(json.dumps(record, indent=2))
        return
    generated = emit_chunks(
        database, emitter, reuse, metrics, args.start, args.through
    )
    print(json.dumps({"status": "GENERATED_UNCHECKED", "chunks": generated}, indent=2))


if __name__ == "__main__":
    main()
