#!/usr/bin/env python3
"""Immutable inputs and append-only output locations for the NF/WPP replay.

The WPP compiler is intentionally an extension of the completed Choice replay.
Nothing in this module discovers an input by globbing: every authoritative
source or accepted Choice artifact is named and hash-pinned here.
"""

from __future__ import annotations

import hashlib
from pathlib import Path


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]

ENDPOINT = "wppfiniteblocknotwppndv"

WPP_SOURCE = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/source_repair/hnwcut_resisomr_assist/"
    "endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.mm"
)
WPP_SOURCE_SHA256 = (
    "868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F"
)
WPP_SOURCE_AUDIT = WPP_SOURCE.with_suffix(".audit.json")
WPP_SOURCE_AUDIT_SHA256 = (
    "695E1D0E4D48ACDBC6BD72919E0D56E504AB2BFEF60530283FBAFF2CEA5DE57F"
)

CHOICE_SOURCE = (
    WORKSPACE
    / "work/mm0_definition_conversion_2026-08-21/binding_metadata/"
    "set_mm_repo/nf.mm"
)
CHOICE_SOURCE_SHA256 = (
    "727A3707545E13EC53F03502EB07DC4635A8C176F275D4014A17FBD823E66083"
)
CHOICE_ENDPOINT = "nchoice"

CHOICE_COMPILER = WORKSPACE / "work/nf_choice_clean_fol_2026-08-21/compiler"
CHOICE_GENERATED = CHOICE_COMPILER / "full_compact_replay_001/generated"
CHOICE_HANDOFF_INVENTORY = (
    CHOICE_COMPILER
    / "full_compact_replay_001/final_handoff_001/resource_inventory.json"
)
CHOICE_HANDOFF_INVENTORY_SHA256 = (
    "0D4635A97199E1F9EB626E90885B01D121EDF43A5078CCAD9554F842667FC815"
)

# The exact intersection reaches chunk 34 and has no member in chunk 35.
# Importing this accepted umbrella therefore exposes every reusable ``g_*``
# theorem without inheriting the five nchoice-tail theorems.
CHOICE_REUSE_MODULE = "FullCompactReplayChunk034Split"
CHOICE_REUSE_NAMESPACE = "NFChoice.Compiler.FullCompactReplay"
CHOICE_REUSE_SOURCE = (
    CHOICE_COMPILER
    / "full_compact_replay_001/split_chunks/chunk_034_003/generated/"
    "FullCompactReplayChunk034Split.lean"
)
CHOICE_REUSE_SOURCE_SHA256 = (
    "94365D9CC7EB784A0CBF9D28F91E09C0AAD14786F46AA8400241457881E751BF"
)
CHOICE_REUSE_AUDIT_DIR = (
    CHOICE_COMPILER
    / "full_compact_replay_001/split_chunks/chunk_034_003/audits/audit_001"
)
CHOICE_REUSE_OLEAN = CHOICE_REUSE_AUDIT_DIR / "FullCompactReplayChunk034Split.olean"
CHOICE_REUSE_OLEAN_SHA256 = (
    "2E1B455D7EE78205E6401588862C58327BAC46E1BDE46B46746E06ACBDF53FCB"
)
CHOICE_REUSE_RESOURCE = CHOICE_REUSE_AUDIT_DIR / "resource.json"
CHOICE_REUSE_RESOURCE_SHA256 = (
    "2551C96F7529755E57517B7A026C2751F5F1A44011B69802CB8F84CC8B45204F"
)

GENERATED = HERE / "generated"
REUSE_MANIFEST = GENERATED / "choice_reuse_manifest_003.json"
METRICS = GENERATED / "wpp_extension_metrics_002.json"
METRICS_AUDIT = HERE / "audits/metrics_002/resource.json"
MISSING_LEAVES = GENERATED / "wpp_missing_leaves_002.json"
REPLAY_OUT = HERE / "full_compact_replay_001/generated"

WPP_DEFINITION_LEAVES = HERE.parent / "definition_leaves"
WPP_SURFACE_AUDIT_DIR = WPP_DEFINITION_LEAVES / "audit_surface_002"
WPP_SURFACE_RESOURCE = WPP_SURFACE_AUDIT_DIR / "resource.json"
WPP_SURFACE_RESOURCE_SHA256 = (
    "159FDCABBE2DF48B82EC04AE37C1E81F3ED2BF03616B43BD8B936AE02069BD38"
)
WPP_SYNTAX_MODULE = "WPPCompactSourceSyntax"
WPP_SYNTAX_OLEAN = WPP_SURFACE_AUDIT_DIR / "WPPCompactSourceSyntax.olean"
WPP_SYNTAX_OLEAN_SHA256 = (
    "F73CB574E37366290EF72A35FC4379D0504A3213D4DCDAB33CA7E941AC5CFC21"
)
WPP_SYNTAX_MANIFEST = (
    WPP_DEFINITION_LEAVES / "generated/wpp_compact_source_syntax_manifest.json"
)
WPP_SYNTAX_MANIFEST_SHA256 = (
    "D692CEB8ECB2ACC8FC0751ABB079D878451CB7260EFBAD914B6D58B6A563A4B0"
)
WPP_FV_MODULE = "WPPCompactSyntaxFVExplicit"
WPP_FV_OLEAN = WPP_SURFACE_AUDIT_DIR / "WPPCompactSyntaxFVExplicit.olean"
WPP_FV_OLEAN_SHA256 = (
    "A06A5CCF7C0F45359C0D26D10ABD0C58887AD7FC59434136835FEAF6BF34F689"
)
WPP_FV_MANIFEST = (
    WPP_DEFINITION_LEAVES
    / "generated/wpp_compact_syntax_fv_explicit_manifest.json"
)
WPP_FV_MANIFEST_SHA256 = (
    "C9F50E461223DCA894313EB229071E7C60AF1720C803DF4A6E4C0F12B46F8DDF"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def require_sha256(path: Path, expected: str, description: str) -> None:
    if not path.is_file():
        raise RuntimeError(f"missing {description}: {path}")
    actual = sha256_file(path)
    if actual != expected:
        raise RuntimeError(
            f"{description} SHA256 mismatch: expected {expected}, got {actual}: {path}"
        )


def verify_pinned_inputs() -> None:
    require_sha256(WPP_SOURCE, WPP_SOURCE_SHA256, "authoritative repaired WPP source")
    require_sha256(WPP_SOURCE_AUDIT, WPP_SOURCE_AUDIT_SHA256, "WPP source audit")
    require_sha256(CHOICE_SOURCE, CHOICE_SOURCE_SHA256, "canonical Choice source")
    require_sha256(
        CHOICE_HANDOFF_INVENTORY,
        CHOICE_HANDOFF_INVENTORY_SHA256,
        "completed Choice handoff inventory",
    )
    require_sha256(CHOICE_REUSE_SOURCE, CHOICE_REUSE_SOURCE_SHA256, "Choice reuse source")
    require_sha256(CHOICE_REUSE_OLEAN, CHOICE_REUSE_OLEAN_SHA256, "Choice reuse olean")
    require_sha256(
        CHOICE_REUSE_RESOURCE,
        CHOICE_REUSE_RESOURCE_SHA256,
        "Choice reuse kernel resource",
    )


def verify_surface_inputs() -> None:
    require_sha256(
        WPP_SURFACE_RESOURCE, WPP_SURFACE_RESOURCE_SHA256, "WPP compact surface audit"
    )
    require_sha256(WPP_SYNTAX_OLEAN, WPP_SYNTAX_OLEAN_SHA256, "WPP syntax olean")
    require_sha256(
        WPP_SYNTAX_MANIFEST, WPP_SYNTAX_MANIFEST_SHA256, "WPP syntax manifest"
    )
    require_sha256(WPP_FV_OLEAN, WPP_FV_OLEAN_SHA256, "WPP explicit FV olean")
    require_sha256(WPP_FV_MANIFEST, WPP_FV_MANIFEST_SHA256, "WPP FV manifest")
