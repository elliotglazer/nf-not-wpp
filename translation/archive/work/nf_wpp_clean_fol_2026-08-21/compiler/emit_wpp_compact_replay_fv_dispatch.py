#!/usr/bin/env python3
"""Append-only WPP replay emitter with manifest-driven FV lemma dispatch.

The completed Choice emitter correctly names FV lemmas for Choice definition
heads, but cannot know that each of the 143 WPP-only heads lives in
``WPPCompactSyntaxFVExplicit``.  This revision derives the exact fully
qualified lemma for every WPP head from the frozen surface manifest and
rewrites both recursive and root structural-FV requests.  Choice/core heads
continue to use the inherited implementation unchanged.
"""

from __future__ import annotations

import json

import emit_wpp_compact_replay as base
from wpp_config import (
    WPP_FV_MANIFEST,
    WPP_FV_MANIFEST_SHA256,
    sha256_file,
)


# Preserve the small public surface consumed by bounded source-oracle emitters.
INTRA_THEOREM_LIFT_PROOF_OPS = base.INTRA_THEOREM_LIFT_PROOF_OPS
choice_replay = base.choice_replay
json_bytes = base.json_bytes


class WPPCompactEmitterFVDispatch(base.WPPCompactEmitter):
    def __init__(self, *args, **kwargs) -> None:  # type: ignore[no-untyped-def]
        super().__init__(*args, **kwargs)
        if sha256_file(WPP_FV_MANIFEST) != WPP_FV_MANIFEST_SHA256:
            raise base.MMError("WPP FV manifest SHA mismatch")
        manifest = json.loads(WPP_FV_MANIFEST.read_text(encoding="utf-8"))
        if (
            manifest.get("status") != "GENERATED_UNCHECKED"
            or manifest.get("namespace")
            != "NFChoice.Compiler.WPPCompactSyntaxFVExplicit"
            or manifest.get("definition_count") != 143
        ):
            raise base.MMError("unexpected WPP FV manifest")
        label_to_lemma = manifest.get("label_to_lemma")
        if not isinstance(label_to_lemma, dict) or len(label_to_lemma) != 143:
            raise base.MMError("WPP FV manifest does not contain 143 exact labels")
        self.wpp_fv_lemma_by_head: dict[tuple[str, str], str] = {}
        self.wpp_fv_lemma_rewrite: dict[str, str] = {}
        for label, value in label_to_lemma.items():
            rule = self.rule_by_label.get(str(label))
            if rule is None:
                raise base.MMError(f"WPP FV rule missing from endpoint closure: {label}")
            lemma = str(value)
            expected_suffix = f".fv_syn_{base.choice_replay.safe(rule.target_head)}"
            if not lemma.endswith(expected_suffix):
                raise base.MMError(f"WPP FV lemma/head mismatch: {label}: {lemma}")
            key = (rule.target_sort, rule.target_head)
            if key in self.wpp_fv_lemma_by_head:
                raise base.MMError(f"duplicate WPP FV target head: {key}")
            self.wpp_fv_lemma_by_head[key] = lemma
            choice_name = (
                "NFChoice.Compiler.CompactSyntaxFVExplicit."
                f"fv_syn_{base.choice_replay.safe(rule.target_head)}"
            )
            self.wpp_fv_lemma_rewrite[choice_name] = lemma
        if len(self.wpp_fv_lemma_by_head) != 143:
            raise base.MMError("incomplete WPP FV head dispatch")

    def fv_lemmas(self, tree: base.AST) -> tuple[str, ...]:
        return tuple(
            self.wpp_fv_lemma_rewrite.get(lemma, lemma)
            for lemma in super().fv_lemmas(tree)
        )

    def _head_fv_support(self, tree: base.AST) -> tuple[str, tuple]:
        lemma, support = super()._head_fv_support(tree)
        return self.wpp_fv_lemma_rewrite.get(lemma, lemma), support


def load_frontend(
    leaf_manifests: tuple[base.Path, ...],
) -> tuple[
    base.Database,
    base.ASTReplayer,
    WPPCompactEmitterFVDispatch,
    dict[str, object],
    dict[str, object],
]:
    base.verify_pinned_inputs()
    base.verify_surface_inputs()
    reuse = json.loads(base.REUSE_MANIFEST.read_text(encoding="utf-8"))
    metrics = json.loads(base.METRICS.read_text(encoding="utf-8"))
    if reuse.get("status") != "PASS" or metrics.get("status") != "MEASURED":
        raise base.MMError("reuse/metrics prerequisite is not frozen PASS")
    if reuse["wpp_source"]["sha256"] != base.WPP_SOURCE_SHA256:
        raise base.MMError("reuse source mismatch")
    if metrics["reuse_manifest_sha256"] != base.sha256_file(base.REUSE_MANIFEST):
        raise base.MMError("metrics/reuse manifest mismatch")
    entries = {str(entry["label"]): entry for entry in reuse["entries"]}
    if len(entries) != 2925:
        raise base.MMError("reuse manifest does not contain 2925 unique labels")
    database = base.Database()
    database.parse(base.WPP_SOURCE)
    replayer = base.ASTReplayer(database, base.Grammar(database))
    audit = replayer.replay_closure(base.ENDPOINT)
    if audit.endpoint_ast.sexpr() != "(wn wwpp)":
        raise base.MMError(f"unexpected WPP endpoint AST {audit.endpoint_ast.sexpr()}")
    emitter = WPPCompactEmitterFVDispatch(database, replayer, entries, leaf_manifests)
    return database, replayer, emitter, reuse, metrics
