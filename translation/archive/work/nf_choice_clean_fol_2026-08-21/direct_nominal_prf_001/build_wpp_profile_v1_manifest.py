#!/usr/bin/env python3
"""Build the frozen static-input inventory for ``WPP_PROFILE_V1``.

This packaging utility is source-only and never invokes Lean.  It discovers
the current NF/WPP backend through the already pinned translator, then writes
one append-only manifest containing workspace-relative paths, byte counts, and
SHA-256 values for every non-runtime file the profile imports or reads.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
from typing import Any


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
CHOICE_COMPILER = HERE.parent / "compiler"
WPP_COMPILER = (
    WORKSPACE / "work" / "nf_wpp_clean_fol_2026-08-21" / "compiler"
)
OUT = HERE / "WPP_PROFILE_V1.json"
THIS = Path(__file__).resolve()

for root in (HERE, CHOICE_COMPILER, WPP_COMPILER):
    value = str(root)
    if value not in sys.path:
        sys.path.insert(0, value)

import reusable_nominal_mm_translator_v1 as cli  # noqa: E402


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_sha256(value: object) -> str:
    return sha256_bytes(
        json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ).encode("utf-8")
    )


def relative(path: Path) -> str:
    resolved = path.resolve()
    if not resolved.is_relative_to(WORKSPACE):
        raise RuntimeError(f"profile input escapes workspace: {resolved}")
    return resolved.relative_to(WORKSPACE).as_posix()


def main() -> int:
    backend = cli.load_backend()
    choice = backend.wpp_base.choice_replay
    entries: list[dict[str, Any]] = []
    by_path: dict[str, dict[str, Any]] = {}

    def add(
        identifier: str,
        path: Path,
        kind: str,
        phase: str,
        read_by: str,
        *,
        module: str | None = None,
    ) -> str:
        path = path.resolve()
        if not path.is_file():
            raise RuntimeError(f"missing profile input: {path}")
        rel = relative(path)
        prior = by_path.get(rel)
        if prior is not None:
            if identifier != prior["id"]:
                raise RuntimeError(
                    f"one profile file has two identifiers: {rel}: "
                    f"{prior['id']} / {identifier}"
                )
            if phase not in prior["phases"]:
                prior["phases"].append(phase)
            if read_by not in prior["readBy"]:
                prior["readBy"].append(read_by)
            return identifier
        entry: dict[str, Any] = {
            "id": identifier,
            "root": "workspace",
            "path": rel,
            "kind": kind,
            "phases": [phase],
            "readBy": [read_by],
            "bytes": path.stat().st_size,
            "sha256": sha256(path),
        }
        if module is not None:
            entry["module"] = module
        entries.append(entry)
        by_path[rel] = entry
        return identifier

    python_modules = (
        "compact_fv_normalize_mixin_v1",
        "emit_nominal_replay",
        "nominal_alpha_dispatch_core_v2",
        "mm_parser",
        "ast_replay",
        "syntax",
        "definitions",
        "emit_source_native_smoke",
        "emit_full_compact_replay",
        "emit_recanonicalization_smoke",
        "emit_compact_fv",
        "wpp_config",
        "emit_wpp_compact_replay",
        "emit_wpp_compact_replay_fv_dispatch",
        "emit_wpp_compact_replay_fv_dispatch_v2",
        "emit_wpp_compact_replay_fv_dispatch_v3",
        "emit_wpp_compact_replay_fv_dispatch_v4",
        "emit_wpp_compact_replay_fv_dispatch_v5",
    )
    for module_name in python_modules:
        module = sys.modules.get(module_name)
        module_path = getattr(module, "__file__", None)
        if not module_path:
            raise RuntimeError(f"backend did not load expected module: {module_name}")
        add(
            f"python:{module_name}",
            Path(module_path),
            "python-module-source",
            "backend-import",
            "Python import graph",
            module=module_name,
        )

    # Core v2 executes v1 through importlib without registering it in
    # ``sys.modules``.  It is therefore named explicitly in the closure.
    add(
        "python:nominal_alpha_dispatch_core_v1_pinned",
        HERE / "nominal_alpha_dispatch_core_v1.py",
        "python-module-source",
        "backend-import",
        "nominal_alpha_dispatch_core_v2 dynamic import",
        module="nominal_alpha_dispatch_core_v1_pinned",
    )

    add(
        "data:nominal-alpha-global-call-map",
        backend.alpha_core.MANIFEST,
        "json-call-map",
        "backend-import",
        "nominal_alpha_dispatch_core_v1 import-time call map",
    )
    add(
        "data:choice-definition-dispatch",
        choice.DISPATCH,
        "json-definition-dispatch",
        "emitter-construction",
        "ParameterizedNominalStructuralEmitter.dispatch",
    )
    add(
        "data:choice-exact-df-calls",
        choice.EXACT_DF_CALLS,
        "json-definition-calls",
        "emitter-construction",
        "ParameterizedNominalStructuralEmitter.exact_df_calls",
    )

    alpha_ids: list[str] = []
    for ordinal, alpha_manifest in enumerate(choice.ALPHA_CALL_MANIFESTS, start=1):
        identifier = f"data:choice-alpha-call-manifest-{ordinal:03d}"
        alpha_ids.append(
            add(
                identifier,
                alpha_manifest,
                "json-alpha-definition-calls",
                "emitter-construction",
                "ParameterizedNominalStructuralEmitter.exact_df_calls",
            )
        )

    add(
        "data:wpp-surface-kernel-resource",
        backend.wpp_config.WPP_SURFACE_RESOURCE,
        "json-accepted-evidence",
        "surface-preflight",
        "wpp_config.verify_surface_inputs",
    )
    add(
        "data:wpp-source-syntax-olean",
        backend.wpp_config.WPP_SYNTAX_OLEAN,
        "binary-accepted-evidence",
        "surface-preflight",
        "wpp_config.verify_surface_inputs",
    )
    add(
        "data:wpp-source-syntax-manifest",
        backend.wpp_config.WPP_SYNTAX_MANIFEST,
        "json-syntax-manifest",
        "surface-preflight",
        "wpp_config.verify_surface_inputs",
    )
    add(
        "data:wpp-explicit-fv-olean",
        backend.wpp_config.WPP_FV_OLEAN,
        "binary-accepted-evidence",
        "surface-preflight",
        "wpp_config.verify_surface_inputs",
    )
    add(
        "data:wpp-explicit-fv-manifest",
        backend.wpp_config.WPP_FV_MANIFEST,
        "json-fv-manifest",
        "surface-preflight",
        "wpp_config.verify_surface_inputs",
    )
    add(
        "data:wpp-explicit-fv-manifest",
        backend.wpp_config.WPP_FV_MANIFEST,
        "json-fv-manifest",
        "emitter-construction",
        "ParameterizedNominalStructuralEmitter.wpp_fv_lemma_by_head",
    )
    add(
        "data:wpp-authoritative-source-audit",
        backend.wpp_config.WPP_SOURCE_AUDIT,
        "json-accepted-evidence",
        "source-preflight",
        "translator accepted WPP source audit check",
    )

    if len(alpha_ids) != 64:
        raise RuntimeError(
            f"WPP_PROFILE_V1 expected 64 alpha call manifests, got {len(alpha_ids)}"
        )
    if len(entries) != 92:
        raise RuntimeError(
            f"WPP_PROFILE_V1 expected 92 unique static inputs, got {len(entries)}"
        )

    input_contract = [
        {
            key: entry[key]
            for key in ("id", "root", "path", "kind", "bytes", "sha256")
        }
        for entry in entries
    ]
    manifest: dict[str, Any] = {
        "schema": "nf-reusable-nominal-mm-translator-profile-v1",
        "status": "FROZEN_STATIC_INPUT_CLOSURE_SOURCE_ONLY",
        "profileId": "WPP_PROFILE_V1",
        "profileVersion": 1,
        "leanStartedByThisProducer": False,
        "producer": {
            "path": relative(THIS),
            "sha256": sha256(THIS),
        },
        "workspaceRoot": {
            "id": "workspace",
            "resolution": "Path(reusable_nominal_mm_translator_v1.__file__).resolve().parents[2]",
        },
        "scope": {
            "theoryProfile": "accepted NF/WPP syntax, structural FV, primitive leaves, and base alpha ordinals 1-71",
            "staticClosure": "all non-stdlib Python modules and fixed JSON/binary evidence imported or read by the source-only NF/WPP translator path",
            "translatorEntrypointSelfPin": "recorded per output as producer.path/producer.sha256; excluded from this manifest to avoid a manifest/loader hash cycle",
            "leanSupportSources": "excluded because the source-only translator names Lean modules but does not read their sources",
            "runtimeInputs": "excluded here and independently hash-authorized by CLI arguments or recursive resource contracts",
        },
        "contracts": {
            "canonicalWppSourceSha256": backend.wpp_config.WPP_SOURCE_SHA256,
            "wppFvDefinitionCount": 143,
            "alphaBaseEndOrdinal": 71,
            "alphaCallManifestCount": len(alpha_ids),
            "supportImports": list(cli.WPP_SUPPORT_IMPORTS),
        },
        "runtimeAuthorizedInputs": [
            {
                "name": "Metamath source",
                "authorization": "--source plus --source-sha256; includes are rejected",
            },
            {
                "name": "accepted alpha frontier, parent resources, and accepted oleans",
                "authorization": "--alpha-frontier-resource plus SHA-256, exact-three trust-zero schema, and recursively embedded hashes",
            },
            {
                "name": "optional predecessor source/kernel boundary",
                "authorization": "--predecessor-resource plus SHA-256 and recursively checked source/olean hashes",
            },
            {
                "name": "generated output directory",
                "authorization": "append-only staging and byte rehash; not an input",
            },
        ],
        "orderedInputSets": {
            "choiceAlphaCallManifests": alpha_ids,
        },
        "inputCount": len(entries),
        "pythonModuleCount": sum(
            entry["kind"] == "python-module-source" for entry in entries
        ),
        "fixedDataCount": sum(
            entry["kind"] != "python-module-source" for entry in entries
        ),
        "inputSetSha256": canonical_sha256(input_contract),
        "inputs": entries,
    }
    content = (json.dumps(manifest, indent=2) + "\n").encode("utf-8")
    if OUT.exists():
        if OUT.read_bytes() != content:
            raise RuntimeError(f"append-only profile manifest differs: {OUT}")
    else:
        OUT.write_bytes(content)
    print(
        json.dumps(
            {
                "status": "PASS_WPP_PROFILE_V1_MANIFEST_BUILT",
                "path": str(OUT),
                "sha256": sha256(OUT),
                "bytes": OUT.stat().st_size,
                "inputCount": len(entries),
                "pythonModuleCount": manifest["pythonModuleCount"],
                "fixedDataCount": manifest["fixedDataCount"],
                "alphaCallManifestCount": len(alpha_ids),
                "leanStarted": False,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
