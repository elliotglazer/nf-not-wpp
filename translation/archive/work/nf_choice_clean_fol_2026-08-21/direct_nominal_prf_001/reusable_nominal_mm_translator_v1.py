#!/usr/bin/env python3
"""Fail-closed, source-only Metamath-to-nominal-Lean replay CLI.

This is an append-only orchestration layer over the checked Metamath parser,
AST replayer, nominal proof algebra, structural FV compiler, and accepted
alpha-frontier loader.  It never invokes Lean.  Version 1 deliberately targets
the already accepted NF/WPP syntax/FV and primitive-leaf profile, while making
the source path, endpoint, theorem interval, alpha frontier, output directory,
module naming, and byte partition runtime inputs.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys
from types import SimpleNamespace
from typing import Any, Iterable, Mapping, Sequence


HERE = Path(__file__).resolve().parent
WORK = HERE.parents[1]
CHOICE_COMPILER = HERE.parent / "compiler"
WPP_COMPILER = WORK / "nf_wpp_clean_fol_2026-08-21" / "compiler"
THIS = Path(__file__).resolve()

SHA256_RE = re.compile(r"^[0-9A-F]{64}$")
LEAN_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
MODULE_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$"
)
FORBIDDEN_SOURCE_RE = re.compile(
    rb"(?m)^\s*(?:axiom|opaque)\b|\bsorry\b|\badmit\b|"
    rb"\bnative_decide\b|\bunsafe\b"
)
GENERIC_DV_FALLBACK_RE = re.compile(rb"\baesop\b")
DV_CACHE_RE = re.compile(
    rb"(?m)^  have (dv_cache_[0-9]+) : (.*?) := by\s*$"
)

ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

# This is the accepted target profile, not an endpoint/chunk configuration.
# A future profile may replace these imports without changing the CLI.
WPP_SUPPORT_IMPORTS = (
    "WPPCompactSourceSyntax",
    "WPPCompactSyntaxFVExplicit",
    "CompactSyntaxFV",
    "CoreFVSimp",
    "NominalSubstitutionLemmas",
    "NominalDefinitionRefl",
    "NominalNFLiteralBaseFour",
    "NominalNFLiteralXpViaCompletenessDev003",
    "NominalNFLiteralRemainingViaCompletenessDev001",
    "NominalDefinitionLeafHandlersCanonical001",
    "NominalDefinitionLeafHandlersObjExtCompat001",
    "NominalRecanonTransportCompat001",
)
DEFAULT_NAMESPACE = "NFChoice.DirectNominalPrf.WPPReplay"

BACKEND_PINS = {
    (HERE / "compact_fv_normalize_mixin_v1.py").resolve():
        "CA7493053B75FC9B2EDC0F6C16AE31DE07C5F1A52119F15314BD09D3A165BDA4",
    (CHOICE_COMPILER / "mm_parser.py").resolve():
        "D657F2FCA96CDFFD8E61FA2845A324CFBCC18777A48A817B8D718280A005C4B7",
    (CHOICE_COMPILER / "ast_replay.py").resolve():
        "BB7875EC606128B40307D42EE1919A341E31B88F57DD0AB032CCD2C849C22ADF",
    (CHOICE_COMPILER / "syntax.py").resolve():
        "216445BC60A6B50906AB862BD2221F846B2B6D071A74A1280F62227CAEAC9618",
    (CHOICE_COMPILER / "definitions.py").resolve():
        "6B438D6A4F5453E19097E8C5674104D76FF5D92FA6EB71CD892DA3448CA349AC",
    (CHOICE_COMPILER / "emit_full_compact_replay.py").resolve():
        "41B91995BA4B532DD66F28BFD49F70B497CD704D7A2BB9F6C696A4B9B3EC7A2E",
    (HERE / "emit_nominal_replay.py").resolve():
        "CF5545A1F1A7CE37657A1A10E963E08EE593B7479C4EE485A23A5801836330B9",
    (HERE / "nominal_alpha_dispatch_core_v2.py").resolve():
        "78AB2C0DACCB170D121D811B082C8256DE3531369E687ACDE6C46C6675F82FB3",
    (WPP_COMPILER / "emit_wpp_compact_replay.py").resolve():
        "6AB2BBAFD69F91F8985C8EB9F1CC6DA00A136CC3A0B88D0E7D3756BB67FC2AAA",
    (WPP_COMPILER / "emit_wpp_compact_replay_fv_dispatch.py").resolve():
        "775B6606058B6406766570B561A82CB2A3969F8AF6BD4E3A128B042E1DA4CB93",
    (WPP_COMPILER / "emit_wpp_compact_replay_fv_dispatch_v2.py").resolve():
        "F1DB42AFD38C011275B3E78FF5250B829B16C99D6EE9C49F74948E0990AABECC",
    (WPP_COMPILER / "emit_wpp_compact_replay_fv_dispatch_v3.py").resolve():
        "15E2084148E3A817ACEDCCA9FC990B0C07078B09155BFFD93EA140AC254C6F9B",
    (WPP_COMPILER / "emit_wpp_compact_replay_fv_dispatch_v4.py").resolve():
        "60018492645BAFAD416B88020149B9D59AF3239924A5BBB931616742F9F89BEB",
    (WPP_COMPILER / "emit_wpp_compact_replay_fv_dispatch_v5.py").resolve():
        "461A8919699BF0A590CA729CC589E740A278ABD936690323B004FAC21FFA11FC",
}

WPP_PROFILE_V1_MANIFEST = HERE / "WPP_PROFILE_V1.json"
WPP_PROFILE_V1_MANIFEST_SHA256 = (
    "2DC43D9E4C07BE4B712DF4858D4EEFD16FC8D9861B093E7CDDF02EDDFEB2D2D2"
)
WPP_PROFILE_V1_SCHEMA = "nf-reusable-nominal-mm-translator-profile-v1"
WPP_PROFILE_V1_STATUS = "FROZEN_STATIC_INPUT_CLOSURE_SOURCE_ONLY"
WPP_PROFILE_V1_INPUT_COUNT = 92
WPP_PROFILE_V1_PYTHON_COUNT = 19
WPP_PROFILE_V1_FIXED_DATA_COUNT = 73

WPP_PROFILE_V2_MANIFEST = HERE / "WPP_PROFILE_V2.json"
WPP_PROFILE_V2_MANIFEST_SHA256 = (
    "96B6A85D4B5B60023000C49BB40CF4F7DCD679AAF4DB6C796880A684DBF12949"
)
WPP_PROFILE_V2_SCHEMA = "nf-reusable-nominal-mm-translator-profile-v2"
WPP_PROFILE_V2_STATUS = WPP_PROFILE_V1_STATUS
WPP_PROFILE_V2_INPUT_COUNT = 97
WPP_PROFILE_V2_PYTHON_COUNT = 20
WPP_PROFILE_V2_FIXED_DATA_COUNT = 77
WPP_PROFILE_IDS = ("WPP_PROFILE_V1", "WPP_PROFILE_V2")
DEFAULT_WPP_PROFILE = "WPP_PROFILE_V2"

GLOBAL_PREFIX72_CONTRACT = {
    "schema": "nf-wpp-nominal-alpha-global-record-prefix-v3",
    "manifestSha256":
        "733E17BAA3798E165989FE991BF26A0AA69E45A1FAECB9EC7CA711B9FC732E47",
    "globalEndOrdinal": 72,
    "globalRecordCount": 72,
    "baseRecordCount": 71,
    "wppRecordCount": 1,
    "recordOrderSha256":
        "0E5231014445B25C31737A520C4F4516101E27E9BAAEF5543B264DC7388FD0D5",
    "sourceHashOrderSha256":
        "FCDCD473111EAD48A6089E2049C0F273C106733CB90DBE87722C586F65726FFA",
    "acceptedBasePrefix48RecordOrderSha256":
        "8A88DF5DB2DCFD214FFB4835D481C601D66A2030F950E687D8DE42F8B75E95CD",
    "acceptedBasePrefix48SourceHashOrderSha256":
        "5381495822D152AD1FC8127617563BFD0AD19FCB6CF95140DDEB990D3A9220F5",
    "acceptedBasePrefix48ResourceSha256":
        "5299F0DA88C07150FCEBB96F2C04CC0DCDFF6C3FC48265C65BA407BC8DBC9FCA",
    "firstRecord": {
        "globalOrdinal": 1,
        "surface": "base",
        "surfaceOrdinal": 1,
        "label": "df-eu",
    },
    "lastRecord": {
        "globalOrdinal": 72,
        "surface": "wpp",
        "surfaceOrdinal": 1,
        "label": "df-iso",
    },
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=False) + "\n").encode("utf-8")


def canonical_json_sha256(value: object) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return sha256_bytes(payload)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def normalized_sha256(value: str, description: str) -> str:
    result = value.upper()
    require(SHA256_RE.fullmatch(result) is not None,
            f"invalid {description} SHA-256: {value!r}")
    return result


def require_file_hash(path: Path, expected: str, description: str) -> None:
    require(path.is_file(), f"missing {description}: {path}")
    actual = sha256(path)
    require(actual == expected,
            f"{description} SHA-256 mismatch: expected {expected}, got {actual}")


def verify_backend_pins() -> None:
    for path, expected in BACKEND_PINS.items():
        require_file_hash(path, expected, "translator backend input")


def verify_wpp_profile_manifest(
    manifest_path: Path,
    expected_sha256: str,
    roots: Mapping[str, Path] | None = None,
    *,
    profile_id: str = "WPP_PROFILE_V1",
) -> dict[str, Any]:
    """Verify one complete static profile before any backend import/read.

    ``roots`` exists only to make the fail-closed parser testable with a tiny
    synthetic profile.  Production has one relocatable workspace root derived
    from this entrypoint and no environment/glob discovery.
    """

    require(profile_id in WPP_PROFILE_IDS,
            f"unsupported WPP profile: {profile_id!r}")
    profile_version = 1 if profile_id == "WPP_PROFILE_V1" else 2
    profile_schema = (
        WPP_PROFILE_V1_SCHEMA
        if profile_version == 1 else WPP_PROFILE_V2_SCHEMA
    )
    profile_status = (
        WPP_PROFILE_V1_STATUS
        if profile_version == 1 else WPP_PROFILE_V2_STATUS
    )

    manifest_path = manifest_path.resolve()
    expected_sha256 = normalized_sha256(expected_sha256, "WPP profile manifest")
    require_file_hash(manifest_path, expected_sha256, "WPP profile manifest")
    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    require(isinstance(data, dict), "WPP profile manifest is not a JSON object")
    require(data.get("schema") == profile_schema,
            "unexpected WPP profile schema")
    require(data.get("status") == profile_status,
            "WPP profile is not a frozen source-only input closure")
    require(data.get("profileId") == profile_id
            and data.get("profileVersion") == profile_version,
            "unexpected WPP profile identity/version")
    require(data.get("leanStartedByThisProducer") is False,
            "WPP profile incorrectly claims a Lean-producing build")

    root_map = {
        key: value.resolve() for key, value in (
            roots or {"workspace": HERE.parents[2]}
        ).items()
    }
    require(set(root_map) == {"workspace"},
            "WPP profile must use exactly the relocatable workspace root")
    inputs = data.get("inputs")
    require(isinstance(inputs, list) and bool(inputs),
            "WPP profile has no static inputs")
    require(data.get("inputCount") == len(inputs),
            "WPP profile input count changed")

    identifiers: set[str] = set()
    resolved_paths: set[Path] = set()
    by_id: dict[str, Path] = {}
    input_contract: list[dict[str, object]] = []
    python_count = 0
    fixed_data_count = 0
    for index, raw in enumerate(inputs, start=1):
        require(isinstance(raw, Mapping),
                f"WPP profile input {index} is not an object")
        identifier = raw.get("id")
        require(isinstance(identifier, str) and identifier,
                f"WPP profile input {index} has no identifier")
        require(identifier not in identifiers,
                f"duplicate WPP profile input identifier: {identifier}")
        identifiers.add(identifier)
        root_name = raw.get("root")
        require(root_name == "workspace",
                f"unexpected root for WPP profile input {identifier}")
        raw_path = raw.get("path")
        require(isinstance(raw_path, str) and raw_path
                and "\\" not in raw_path and ":" not in raw_path,
                f"invalid portable path for WPP profile input {identifier}")
        relative = PurePosixPath(raw_path)
        require(not relative.is_absolute()
                and all(part not in {"", ".", ".."} for part in relative.parts),
                f"escaping path for WPP profile input {identifier}")
        path = root_map["workspace"].joinpath(*relative.parts).resolve()
        require(path.is_relative_to(root_map["workspace"]),
                f"resolved WPP profile input escapes workspace: {identifier}")
        require(path not in resolved_paths,
                f"duplicate WPP profile input path: {path}")
        resolved_paths.add(path)
        by_id[identifier] = path
        kind = raw.get("kind")
        require(isinstance(kind, str) and kind,
                f"WPP profile input has no kind: {identifier}")
        size = raw.get("bytes")
        require(isinstance(size, int) and not isinstance(size, bool) and size >= 0,
                f"invalid byte count for WPP profile input {identifier}")
        digest = raw.get("sha256")
        require(isinstance(digest, str),
                f"WPP profile input has no SHA-256: {identifier}")
        digest = normalized_sha256(digest, f"WPP profile input {identifier}")
        require(path.is_file(), f"missing WPP profile input: {path}")
        require(path.stat().st_size == size,
                f"WPP profile input byte count changed: {identifier}")
        require_file_hash(path, digest, f"WPP profile input {identifier}")
        if kind == "python-module-source":
            python_count += 1
            module = raw.get("module")
            require(isinstance(module, str) and module,
                    f"Python profile input lacks module name: {identifier}")
        else:
            fixed_data_count += 1
        input_contract.append({
            "id": identifier,
            "root": root_name,
            "path": raw_path,
            "kind": kind,
            "bytes": size,
            "sha256": digest,
        })

    require(data.get("pythonModuleCount") == python_count,
            "WPP profile Python-module count changed")
    require(data.get("fixedDataCount") == fixed_data_count,
            "WPP profile fixed-data count changed")
    require(data.get("inputSetSha256") == canonical_json_sha256(input_contract),
            "WPP profile input-set digest changed")
    ordered = data.get("orderedInputSets")
    require(isinstance(ordered, Mapping),
            "WPP profile has no ordered input sets")
    alpha_order = ordered.get("choiceAlphaCallManifests")
    require(isinstance(alpha_order, list) and len(alpha_order) == 64
            and len(set(alpha_order)) == 64
            and all(identifier in identifiers for identifier in alpha_order),
            "WPP profile alpha-call manifest order changed")
    contracts = data.get("contracts")
    require(isinstance(contracts, Mapping)
            and contracts.get("canonicalWppSourceSha256")
            == "868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F"
            and contracts.get("wppFvDefinitionCount") == 143
            and contracts.get("alphaBaseEndOrdinal") == 71
            and contracts.get("alphaCallManifestCount") == 64
            and contracts.get("supportImports") == list(WPP_SUPPORT_IMPORTS),
            "WPP profile semantic contract changed")

    if profile_version == 2:
        _verify_wpp_profile_v2_extension(data, by_id, root_map["workspace"])

    result = dict(data)
    result["_manifestPath"] = manifest_path
    result["_manifestSha256"] = expected_sha256
    result["_resolvedInputs"] = by_id
    return result


def _verify_wpp_profile_v2_extension(
    data: Mapping[str, Any],
    by_id: Mapping[str, Path],
    workspace: Path,
) -> None:
    """Verify V2's immutable V1 lineage and global72 source metadata."""

    extends = data.get("extends")
    require(isinstance(extends, Mapping)
            and extends.get("profileId") == "WPP_PROFILE_V1"
            and extends.get("profileVersion") == 1
            and extends.get("manifestInputId") == "profile:WPP_PROFILE_V1"
            and extends.get("manifestSha256")
            == WPP_PROFILE_V1_MANIFEST_SHA256
            and extends.get("inputCount") == WPP_PROFILE_V1_INPUT_COUNT
            and extends.get("inheritedEntriesByteExact") is True,
            "WPP_PROFILE_V2 immutable-parent contract changed")
    required_ids = {
        "profile:WPP_PROFILE_V1",
        "python:nominal_alpha_dispatch_core_v3",
        "data:a4972-global-prefix72-source-manifest",
        "data:a4972-global-prefix72-source-audit",
        "data:a4972-global-prefix72-independent-join-audit",
    }
    require(required_ids.issubset(by_id),
            "WPP_PROFILE_V2 extension input set is incomplete")
    v1_path = by_id["profile:WPP_PROFILE_V1"]
    require(v1_path == WPP_PROFILE_V1_MANIFEST.resolve()
            and sha256(v1_path) == WPP_PROFILE_V1_MANIFEST_SHA256,
            "WPP_PROFILE_V2 parent manifest identity changed")
    v1 = json.loads(v1_path.read_text(encoding="utf-8"))
    require(isinstance(v1, Mapping)
            and v1.get("profileId") == "WPP_PROFILE_V1"
            and v1.get("profileVersion") == 1
            and v1.get("inputSetSha256") == extends.get("inputSetSha256")
            and data.get("inputs", [])[:WPP_PROFILE_V1_INPUT_COUNT]
            == v1.get("inputs"),
            "WPP_PROFILE_V2 does not inherit V1 entries byte-exactly")

    contracts = data.get("contracts")
    require(isinstance(contracts, Mapping)
            and contracts.get("alphaGlobalEndOrdinal") == 72
            and contracts.get("alphaGlobalBaseRecordCount") == 71
            and contracts.get("alphaGlobalWppRecordCount") == 1
            and contracts.get("globalAlphaPrefix72")
            == GLOBAL_PREFIX72_CONTRACT,
            "WPP_PROFILE_V2 global-alpha semantic contract changed")
    a4972_contract = contracts.get("a4972SourceMetadata")
    require(isinstance(a4972_contract, Mapping)
            and a4972_contract.get("sourceManifestSha256")
            == "8F55E7A661F33BD4E6ECAE257FCEB314CB7B31113D164681E3FAC192764F7FD5"
            and a4972_contract.get("sourceAuditSha256")
            == "D5B29D8E5BF1B2072924A6B30D97B673CD218A03193C268701C45D2B9C3B5A08"
            and a4972_contract.get("independentJoinAuditSha256")
            == "4A93CA905E684D3E1740D9834744E64B3742711876A3661583E6360A5251A875"
            and a4972_contract.get("successorSourceHashOrderSha256")
            == "F5A3BAD8C928365ACB77E6C442AD7063DE80DDBC0D95B47DC83FA9980302C854"
            and a4972_contract.get("importChainSha256")
            == "157CF0DDB86EBDA8C4EE88973F45616639B890BFAC6C1E8D56521DD268CA192E",
            "WPP_PROFILE_V2 a4972 metadata contract changed")
    expected_w1 = {
        "globalOrdinal": 72,
        "surface": "wpp",
        "surfaceOrdinal": 1,
        "label": "df-iso",
        "module": "NominalAlphaRepairedWpp001001IsoStructural001",
        "sourceSha256":
            "CF76E477A68EE513FDEDFC3F7AC502A0B321BBD8EEFC9666CBE9FF1E3618CB61",
    }
    require(a4972_contract.get("w1") == expected_w1,
            "WPP_PROFILE_V2 W1 identity changed")

    source_path = by_id["data:a4972-global-prefix72-source-manifest"]
    audit_path = by_id["data:a4972-global-prefix72-source-audit"]
    join_path = by_id["data:a4972-global-prefix72-independent-join-audit"]
    require(
        sha256(source_path) == a4972_contract.get("sourceManifestSha256")
        and sha256(audit_path) == a4972_contract.get("sourceAuditSha256")
        and sha256(join_path) == a4972_contract.get("independentJoinAuditSha256"),
        "WPP_PROFILE_V2 a4972 metadata/input identity changed",
    )
    source = json.loads(source_path.read_text(encoding="utf-8"))
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    join = json.loads(join_path.read_text(encoding="utf-8"))
    require(isinstance(source, Mapping)
            and source.get("schema")
            == "nf-wpp-nominal-alpha-global-successor-049-072-v1"
            and source.get("status") == "GENERATED_SOURCE_ONLY_KERNEL_PENDING"
            and source.get("leanStartedByProducer") is False
            and source.get("firstGlobalOrdinal") == 49
            and source.get("lastGlobalOrdinal") == 72
            and source.get("count") == 24
            and source.get("surfaceSequence") == "B49..B71,W1"
            and source.get("globalRecordContract") == GLOBAL_PREFIX72_CONTRACT,
            "WPP_PROFILE_V2 a4972 source manifest changed")
    records = source.get("records")
    require(isinstance(records, list) and len(records) == 24
            and [row.get("globalOrdinal") for row in records]
            == list(range(49, 73))
            and [(row.get("surface"), row.get("surfaceOrdinal")) for row in records]
            == [("base", ordinal) for ordinal in range(49, 72)]
            + [("wpp", 1)]
            and records[-1].get("label") == "df-iso"
            and records[-1].get("module") == expected_w1["module"]
            and records[-1].get("successorSourceSha256")
            == expected_w1["sourceSha256"],
            "WPP_PROFILE_V2 a4972 record sequence changed")
    require(isinstance(audit, Mapping)
            and audit.get("schema")
            == "nf-wpp-nominal-alpha-global-049-072-source-audit-v1"
            and audit.get("status") == "PASS_SOURCE_AUTHORIZED_KERNEL_PENDING"
            and audit.get("leanStartedByAudit") is False
            and audit.get("kernelAcceptanceClaimed") is False
            and audit.get("manifest", {}).get("sha256")
            == a4972_contract.get("sourceManifestSha256")
            and audit.get("globalPrefix72", {}).get("recordContract")
            == GLOBAL_PREFIX72_CONTRACT,
            "WPP_PROFILE_V2 a4972 source audit changed")
    successor = join.get("successor") if isinstance(join, Mapping) else None
    require(isinstance(join, Mapping)
            and join.get("schema")
            == "nf-wpp-nominal-alpha-v3-a4972-independent-source-join-v1"
            and join.get("status")
            == "PASS_SOURCE_ONLY_PREFIX48_COMPAT_GLOBAL49_72_EXACT_KERNEL_PENDING"
            and join.get("leanStartedByThisAudit") is False
            and join.get("kernelAcceptanceClaimed") is False
            and isinstance(successor, Mapping)
            and successor.get("count") == 24
            and successor.get("firstGlobalOrdinal") == 49
            and successor.get("lastGlobalOrdinal") == 72
            and successor.get("surfaceSequence") == "B49..B71,W1"
            and successor.get("sourceHashOrderSha256")
            == a4972_contract.get("successorSourceHashOrderSha256")
            and successor.get("importCount") == 72
            and successor.get("importChainSha256")
            == a4972_contract.get("importChainSha256")
            and successor.get("w1Identity", {}).get("globalOrdinal") == 72
            and successor.get("w1Identity", {}).get("label") == "df-iso"
            and successor.get("w1Identity", {}).get(
                "originalSourceByteIdentical"
            ) is True,
            "WPP_PROFILE_V2 independent a4972 join audit changed")


@lru_cache(maxsize=1)
def load_wpp_profile_v1() -> dict[str, Any]:
    profile = verify_wpp_profile_manifest(
        WPP_PROFILE_V1_MANIFEST, WPP_PROFILE_V1_MANIFEST_SHA256
    )
    require(profile["inputCount"] == WPP_PROFILE_V1_INPUT_COUNT
            and profile["pythonModuleCount"] == WPP_PROFILE_V1_PYTHON_COUNT
            and profile["fixedDataCount"] == WPP_PROFILE_V1_FIXED_DATA_COUNT,
            "WPP_PROFILE_V1 census changed")
    return profile


@lru_cache(maxsize=1)
def load_wpp_profile_v2() -> dict[str, Any]:
    profile = verify_wpp_profile_manifest(
        WPP_PROFILE_V2_MANIFEST,
        WPP_PROFILE_V2_MANIFEST_SHA256,
        profile_id="WPP_PROFILE_V2",
    )
    require(profile["inputCount"] == WPP_PROFILE_V2_INPUT_COUNT
            and profile["pythonModuleCount"] == WPP_PROFILE_V2_PYTHON_COUNT
            and profile["fixedDataCount"] == WPP_PROFILE_V2_FIXED_DATA_COUNT,
            "WPP_PROFILE_V2 census changed")
    return profile


def load_wpp_profile(profile_id: str) -> dict[str, Any]:
    require(profile_id in WPP_PROFILE_IDS,
            f"unsupported WPP profile: {profile_id!r}")
    return (
        load_wpp_profile_v1()
        if profile_id == "WPP_PROFILE_V1" else load_wpp_profile_v2()
    )


def wpp_profile_provenance(profile: Mapping[str, Any]) -> dict[str, object]:
    return {
        "profileId": profile["profileId"],
        "profileVersion": profile["profileVersion"],
        "schema": profile["schema"],
        "status": profile["status"],
        "manifest": str(profile["_manifestPath"]),
        "manifestSha256": profile["_manifestSha256"],
        "inputCount": profile["inputCount"],
        "pythonModuleCount": profile["pythonModuleCount"],
        "fixedDataCount": profile["fixedDataCount"],
        "inputSetSha256": profile["inputSetSha256"],
        "staticInputsVerifiedBeforeBackendImport": True,
        "runtimeInputsIndependentlyHashAuthorized": True,
        "backendImportsForcedFromVerifiedSource": True,
    }


def prepare_verified_profile_imports(profile: Mapping[str, Any]) -> None:
    """Make source hashes, rather than adjacent ``.pyc`` files, executable."""

    for raw in profile["inputs"]:
        if raw["kind"] != "python-module-source":
            continue
        module_name = str(raw["module"])
        # Core v1 is executed under a private name without registration.  V2
        # likewise executes core v2 privately from the verified core-v3 source.
        if module_name == "nominal_alpha_dispatch_core_v1_pinned" or (
            profile.get("profileId") == "WPP_PROFILE_V2"
            and module_name == "nominal_alpha_dispatch_core_v2"
        ):
            continue
        require(module_name not in sys.modules,
                f"WPP profile backend module was preloaded before verification: "
                f"{module_name}")
    cache_prefix = (
        HERE
        / f".wpp-profile-v{profile['profileVersion']}-bytecode-disabled-{os.getpid()}-"
        f"{str(profile['_manifestSha256'])[:16]}"
    )
    require(not cache_prefix.exists(),
            f"reserved verified-source bytecode prefix exists: {cache_prefix}")
    # ``-B`` prevents bytecode writes but still permits reads.  Redirect cache
    # lookup to a process-unique absent tree and also suppress writes, so every
    # local backend import compiles the already verified source bytes.
    sys.dont_write_bytecode = True
    sys.pycache_prefix = str(cache_prefix)


def verify_loaded_backend_profile(
    profile: Mapping[str, Any], backend: SimpleNamespace
) -> None:
    """Join the frozen path inventory to the modules/constants actually used."""

    by_id = profile["_resolvedInputs"]
    require(isinstance(by_id, Mapping), "WPP profile resolved-input map missing")
    for raw in profile["inputs"]:
        if raw["kind"] != "python-module-source":
            continue
        module_name = str(raw["module"])
        if module_name == "nominal_alpha_dispatch_core_v1_pinned" or (
            profile.get("profileId") == "WPP_PROFILE_V2"
            and module_name == "nominal_alpha_dispatch_core_v2"
        ):
            continue
        module = sys.modules.get(module_name)
        actual = getattr(module, "__file__", None)
        require(actual is not None
                and Path(actual).resolve() == by_id[str(raw["id"])],
                f"WPP profile imported unexpected module source: {module_name}")

    choice = backend.wpp_base.choice_replay
    require(Path(choice.DISPATCH).resolve()
            == by_id["data:choice-definition-dispatch"],
            "WPP profile Choice dispatch path changed")
    require(Path(choice.EXACT_DF_CALLS).resolve()
            == by_id["data:choice-exact-df-calls"],
            "WPP profile exact-DF path changed")
    alpha_ids = profile["orderedInputSets"]["choiceAlphaCallManifests"]
    require(
        tuple(Path(path).resolve() for path in choice.ALPHA_CALL_MANIFESTS)
        == tuple(by_id[str(identifier)] for identifier in alpha_ids),
        "WPP profile alpha-call manifest sequence changed",
    )
    require(Path(backend.alpha_core.MANIFEST).resolve()
            == by_id["data:nominal-alpha-global-call-map"],
            "WPP profile global alpha call-map path changed")
    require(Path(backend.wpp_config.WPP_SURFACE_RESOURCE).resolve()
            == by_id["data:wpp-surface-kernel-resource"]
            and Path(backend.wpp_config.WPP_SYNTAX_OLEAN).resolve()
            == by_id["data:wpp-source-syntax-olean"]
            and Path(backend.wpp_config.WPP_SYNTAX_MANIFEST).resolve()
            == by_id["data:wpp-source-syntax-manifest"]
            and Path(backend.wpp_config.WPP_FV_OLEAN).resolve()
            == by_id["data:wpp-explicit-fv-olean"]
            and Path(backend.wpp_config.WPP_FV_MANIFEST).resolve()
            == by_id["data:wpp-explicit-fv-manifest"]
            and Path(backend.wpp_config.WPP_SOURCE_AUDIT).resolve()
            == by_id["data:wpp-authoritative-source-audit"],
            "WPP profile surface/source evidence path changed")
    if profile.get("profileId") == "WPP_PROFILE_V2":
        require(
            Path(backend.alpha_core.__file__).resolve()
            == by_id["python:nominal_alpha_dispatch_core_v3"]
            and backend.alpha_core.global_record_contract(72)
            == GLOBAL_PREFIX72_CONTRACT
            and len(backend.alpha_core.GLOBAL_RECORDS) == 97
            and backend.alpha_core.GLOBAL_RECORDS[71]["label"] == "df-iso",
            "WPP_PROFILE_V2 loaded global-alpha v3 contract changed",
        )


def safe(name: str) -> str:
    result = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if not result or result[0].isdigit():
        result = "n_" + result
    return result


def require_module_name(value: str, description: str) -> str:
    require(MODULE_RE.fullmatch(value) is not None,
            f"invalid Lean {description}: {value!r}")
    return value


def unique(items: Iterable[str]) -> tuple[str, ...]:
    seen: set[str] = set()
    result: list[str] = []
    for item in items:
        if item not in seen:
            seen.add(item)
            result.append(item)
    return tuple(result)


@dataclass(frozen=True)
class Selection:
    start_ordinal: int
    end_ordinal: int
    all_labels: tuple[str, ...]
    selected_labels: tuple[str, ...]
    earlier_labels: tuple[str, ...]


def select_interval(
    labels: Sequence[str], start: int | None, end: int | None
) -> Selection:
    require(bool(labels), "endpoint closure contains no proved |- theorems")
    require((start is None) == (end is None),
            "start/end ordinals must be supplied together")
    first = 1 if start is None else start
    last = len(labels) if end is None else end
    require(1 <= first <= last <= len(labels),
            f"ordinal interval must satisfy 1 <= start <= end <= {len(labels)}")
    all_labels = tuple(labels)
    return Selection(
        first,
        last,
        all_labels,
        all_labels[first - 1:last],
        all_labels[:first - 1],
    )


def group_blocks(blocks: Sequence[bytes], limit: int) -> tuple[tuple[int, int], ...]:
    require(limit > 0, "split byte limit must be positive")
    require(bool(blocks), "cannot partition an empty theorem sequence")
    groups: list[tuple[int, int]] = []
    begin = 0
    running = 0
    for index, block in enumerate(blocks):
        require(bool(block), f"empty theorem block at index {index}")
        if index > begin and running + len(block) > limit:
            groups.append((begin, index))
            begin = index
            running = 0
        running += len(block)
    groups.append((begin, len(blocks)))
    require(groups[0][0] == 0 and groups[-1][1] == len(blocks),
            "theorem partition does not cover every block")
    require(all(groups[i][1] == groups[i + 1][0]
                for i in range(len(groups) - 1)),
            "theorem partition is not contiguous")
    require(all(begin < end for begin, end in groups),
            "theorem partition contains an empty part")
    return tuple(groups)


@dataclass(frozen=True)
class PredecessorContract:
    resource: Path
    resource_sha256: str
    status: str
    source_sha256: str
    endpoint: str
    end_theorem_ordinal: int
    module: str
    boundary_kind: str
    source_resource: Path
    source_resource_sha256: str
    source_artifact: Path
    source_artifact_sha256: str
    kernel_artifact: Path | None
    kernel_artifact_sha256: str | None


def resource_relative_path(
    value: Any, resource: Path, description: str
) -> Path:
    require(isinstance(value, str) and value,
            f"predecessor resource has no {description} path")
    path = Path(value)
    if not path.is_absolute():
        path = resource.parent / path
    return path.resolve()


def resource_sha256_field(
    value: Any, description: str
) -> str:
    require(isinstance(value, str),
            f"predecessor resource has no {description} SHA-256")
    return normalized_sha256(value, description)


def source_predecessor_contract_from_data(
    data: Mapping[str, Any], resource: Path, resource_sha256: str
) -> PredecessorContract:
    status = str(data.get("status", ""))
    require(
        status.startswith("PASS_SOURCE_ONLY")
        or status.startswith("GENERATED_SOURCE_ONLY"),
        "predecessor source resource is not a successful source-only boundary",
    )
    source_hash = (
        data.get("exact_wpp_source_sha256")
        or data.get("exactWppSourceSha256")
        or data.get("source_sha256")
        or data.get("sourceSha256")
    )
    endpoint = data.get("endpoint")
    end_ordinal = data.get("end_theorem_ordinal")
    if end_ordinal is None:
        end_ordinal = data.get("endTheoremOrdinal")
    if end_ordinal is None:
        end_ordinal = data.get("prefixTheoremCount")

    artifact: Any = data.get("compatibility_module")
    if not isinstance(artifact, Mapping):
        artifact = data.get("umbrella_module")
    if not isinstance(artifact, Mapping):
        artifact = data.get("umbrellaModule")
    require(isinstance(artifact, Mapping),
            "predecessor source resource has no umbrella source artifact")
    module = artifact.get("module")
    artifact_path = resource_relative_path(
        artifact.get("source"), resource, "umbrella source artifact"
    )
    artifact_hash = resource_sha256_field(
        artifact.get("source_sha256") or artifact.get("sourceSha256"),
        "umbrella source artifact",
    )

    require(isinstance(source_hash, str) and SHA256_RE.fullmatch(source_hash.upper()),
            "predecessor resource has no exact source SHA-256")
    require(isinstance(endpoint, str) and endpoint,
            "predecessor resource has no endpoint")
    require(isinstance(end_ordinal, int) and end_ordinal >= 1,
            "predecessor resource has no positive ending theorem ordinal")
    require(isinstance(module, str),
            "predecessor resource has no compatibility/umbrella module")
    require_module_name(module, "predecessor module")
    require_file_hash(
        artifact_path, artifact_hash, "predecessor umbrella source artifact"
    )
    return PredecessorContract(
        resource,
        resource_sha256,
        status,
        source_hash.upper(),
        endpoint,
        end_ordinal,
        module,
        "source-only",
        resource,
        resource_sha256,
        artifact_path,
        artifact_hash,
        None,
        None,
    )


def kernel_source_resource_reference(
    data: Mapping[str, Any]
) -> tuple[Any, Any]:
    reference: Any = data.get("sourceResource")
    if not isinstance(reference, Mapping):
        dependencies = data.get("dependencyPins")
        if isinstance(dependencies, Mapping):
            reference = dependencies.get("generatedSourceResource")
    if isinstance(reference, Mapping):
        return (
            reference.get("path") or reference.get("resource"),
            reference.get("sha256") or reference.get("resourceSha256"),
        )
    return data.get("splitResource"), data.get("splitResourceSha256")


def kernel_predecessor_contract_from_data(
    data: Mapping[str, Any], resource: Path, resource_sha256: str
) -> PredecessorContract:
    status = str(data.get("status", ""))
    require(
        status.startswith(("PASS_TRUST0_", "PASS_TRUST_ZERO_", "PASS_KERNEL_"))
        and "EXACT_THREE" in status,
        "predecessor kernel resource is not an exact-three trust-zero boundary",
    )
    command = data.get("umbrellaCommand")
    require(isinstance(command, Mapping),
            "predecessor kernel resource has no umbrellaCommand artifact")
    require(command.get("trust") == 0 and command.get("trust") is not False,
            "predecessor umbrella command was not checked at trust zero")
    require(command.get("exitCode") == 0 and command.get("exitCode") is not False,
            "predecessor umbrella command did not exit successfully")
    require(command.get("killed") is False,
            "predecessor umbrella command was killed or lacks kill evidence")
    require(command.get("exactAllowedThree") is True,
            "predecessor umbrella command lacks exact-three evidence")

    source_resource_value, source_resource_hash_value = (
        kernel_source_resource_reference(data)
    )
    source_resource = resource_relative_path(
        source_resource_value, resource, "kernel source resource"
    )
    source_resource_hash = resource_sha256_field(
        source_resource_hash_value, "kernel source resource"
    )
    require_file_hash(
        source_resource, source_resource_hash, "predecessor kernel source resource"
    )
    source_data = json.loads(source_resource.read_text(encoding="utf-8"))
    require(isinstance(source_data, dict),
            "predecessor kernel source resource is not a JSON object")
    source_contract = source_predecessor_contract_from_data(
        source_data, source_resource, source_resource_hash
    )

    command_module = command.get("module")
    require(command_module == source_contract.module,
            "predecessor kernel/source umbrella modules differ")
    command_source = resource_relative_path(
        command.get("source"), resource, "kernel umbrella source"
    )
    command_source_hash = resource_sha256_field(
        command.get("sourceSha256") or command.get("source_sha256"),
        "kernel umbrella source",
    )
    require(command_source == source_contract.source_artifact,
            "predecessor kernel command names a different umbrella source")
    require(command_source_hash == source_contract.source_artifact_sha256,
            "predecessor kernel/source umbrella hashes differ")
    require_file_hash(
        command_source, command_source_hash, "predecessor kernel umbrella source"
    )

    output = resource_relative_path(
        command.get("output"), resource, "kernel umbrella output"
    )
    output_hash = resource_sha256_field(
        command.get("outputSha256") or command.get("output_sha256"),
        "kernel umbrella output",
    )
    require_file_hash(output, output_hash, "predecessor kernel umbrella output")

    outer_source_hash = (
        data.get("exact_wpp_source_sha256")
        or data.get("exactWppSourceSha256")
        or data.get("source_sha256")
        or data.get("sourceSha256")
    )
    if outer_source_hash is not None:
        require(
            resource_sha256_field(outer_source_hash, "kernel exact source")
            == source_contract.source_sha256,
            "predecessor kernel/source exact source hashes differ",
        )
    if data.get("endpoint") is not None:
        require(data.get("endpoint") == source_contract.endpoint,
                "predecessor kernel/source endpoints differ")
    outer_end = data.get("end_theorem_ordinal")
    if outer_end is None:
        outer_end = data.get("endTheoremOrdinal")
    if outer_end is not None:
        require(outer_end == source_contract.end_theorem_ordinal,
                "predecessor kernel/source ending ordinals differ")

    return PredecessorContract(
        resource,
        resource_sha256,
        status,
        source_contract.source_sha256,
        source_contract.endpoint,
        source_contract.end_theorem_ordinal,
        source_contract.module,
        "kernel-trust-zero-exact-three",
        source_resource,
        source_resource_hash,
        source_contract.source_artifact,
        source_contract.source_artifact_sha256,
        output,
        output_hash,
    )


def predecessor_contract_from_data(
    data: Mapping[str, Any], resource: Path, resource_sha256: str
) -> PredecessorContract:
    if isinstance(data.get("umbrellaCommand"), Mapping):
        return kernel_predecessor_contract_from_data(
            data, resource, resource_sha256
        )
    return source_predecessor_contract_from_data(
        data, resource, resource_sha256
    )


def load_predecessor(
    path: Path,
    expected_sha256: str,
    source_sha256: str,
    endpoint: str,
    expected_end_ordinal: int,
) -> PredecessorContract:
    path = path.resolve()
    require_file_hash(path, expected_sha256, "predecessor resource")
    data = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(data, dict), "predecessor resource is not a JSON object")
    result = predecessor_contract_from_data(data, path, expected_sha256)
    require(result.source_sha256 == source_sha256,
            "predecessor source SHA-256 differs from selected source")
    require(result.endpoint == endpoint,
            "predecessor endpoint differs from selected endpoint")
    require(result.end_theorem_ordinal == expected_end_ordinal,
            "predecessor does not end immediately before selected interval")
    return result


@lru_cache(maxsize=2)
def load_backend(profile_id: str = "WPP_PROFILE_V1") -> SimpleNamespace:
    profile = load_wpp_profile(profile_id)
    prepare_verified_profile_imports(profile)
    verify_backend_pins()
    for root in (HERE, CHOICE_COMPILER, WPP_COMPILER):
        value = str(root)
        if value not in sys.path:
            sys.path.insert(0, value)

    import emit_nominal_replay as nominal
    import emit_wpp_compact_replay as wpp_base
    import emit_wpp_compact_replay_fv_dispatch as fv_v1
    import emit_wpp_compact_replay_fv_dispatch_v5 as structural
    import compact_fv_normalize_mixin_v1 as compact_fv
    if profile_id == "WPP_PROFILE_V2":
        import nominal_alpha_dispatch_core_v3 as alpha_core
    else:
        import nominal_alpha_dispatch_core_v2 as alpha_core
    import wpp_config
    from ast_replay import ASTReplayer
    from mm_parser import Database, MMError, tokenize_text
    from syntax import Grammar

    backend = SimpleNamespace(
        nominal=nominal,
        wpp_base=wpp_base,
        fv_v1=fv_v1,
        structural=structural,
        compact_fv=compact_fv,
        alpha_core=alpha_core,
        wpp_config=wpp_config,
        ASTReplayer=ASTReplayer,
        Database=Database,
        MMError=MMError,
        tokenize_text=tokenize_text,
        Grammar=Grammar,
    )
    verify_loaded_backend_profile(profile, backend)
    return backend


def exact_three_alpha_resource(data: Mapping[str, Any]) -> bool:
    audit = data.get("audit")
    if not isinstance(audit, Mapping):
        return False
    exact = (
        audit.get("exactAllowedThreeAll") is True
        or audit.get("exactAllowedThree") is True
    )
    if not exact:
        return False
    # New compact/global frontier resources publish one kernel-audit record
    # instead of duplicating its `#print axioms` result as `axiomReports`.
    # Accept that schema only with its full fail-closed success contract and
    # the exact top-level allow-list.  Older frontiers continue through the
    # report-based branches below.
    compact_exact_three = (
        data.get("allowedAxioms") == list(ALLOWED_AXIOMS)
        and audit.get("exitCode") == 0
        and audit.get("killed") is False
        and audit.get("emptyStderr") is True
        and audit.get("forbiddenAxiomMatches") == []
    )
    if compact_exact_three:
        return True
    reports = audit.get("axiomReports") or audit.get("reports")
    expected = sorted(ALLOWED_AXIOMS)
    if reports is not None:
        return (
            isinstance(reports, list)
            and bool(reports)
            and all(
                isinstance(report, Mapping)
                and isinstance(report.get("axioms"), list)
                and sorted(str(x) for x in report["axioms"]) == expected
                for report in reports
            )
        )
    reported_axioms = audit.get("reportedAxioms")
    return (
        isinstance(reported_axioms, list)
        and bool(reported_axioms)
        and all(isinstance(axiom, str) for axiom in reported_axioms)
        and sorted(reported_axioms) == expected
    )


def require_no_metamath_includes(tokens: Sequence[str]) -> None:
    require(
        "$[" not in tokens,
        "Metamath includes are unsupported in translator v1; "
        "supply one flattened, hash-pinned source file",
    )


def require_supported_leaf_coverage(
    missing: Sequence[Mapping[str, Any]]
) -> None:
    require(
        not missing,
        "unsupported leaf at selected frontier: "
        + (json.dumps(missing[0]) if missing else "<none>"),
    )


def _workspace_resource_path(value: str | Path) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = HERE.parents[2] / path
    return path.resolve()


def reconcile_recursive_alpha_imports(
    frontier: Any,
    resource: Path,
    expected_sha256: str,
) -> None:
    """Recover accepted module overrides from the full frontier ancestry.

    The legacy v2 alpha loader collects olean roots recursively but only
    collects module-name overrides from the newest resource.  A compact
    successor such as prefix 49 therefore has all the right oleans while its
    import tuple silently falls back to obsolete canonical names at 34..48.
    Reconcile the names against the same hash-pinned ancestry and require each
    changed import to resolve to its declared, hash-matching olean.
    """

    end_ordinal = frontier.end_ordinal
    require(isinstance(end_ordinal, int) and not isinstance(end_ordinal, bool),
            "alpha frontier end ordinal is not an integer")
    imports = list(frontier.imports)
    require(len(imports) == end_ordinal,
            "alpha frontier import count changed")
    roots = tuple(Path(path).resolve() for path in frontier.olean_roots)
    overrides: dict[int, str] = {}
    outputs: dict[str, tuple[Path, str]] = {}
    seen: set[Path] = set()

    def visit(path: Path, expected: str) -> None:
        path = path.resolve()
        require(path not in seen, "alpha frontier parent cycle")
        seen.add(path)
        require_file_hash(path, expected, "alpha frontier ancestry resource")
        data = json.loads(path.read_text(encoding="utf-8"))
        require(isinstance(data, Mapping),
                "alpha frontier ancestry resource is not an object")
        for key in ("compiles", "acceptedModules", "moduleOverrides"):
            rows = data.get(key, []) or []
            require(isinstance(rows, list),
                    f"alpha frontier {key} is not a list")
            for row in rows:
                require(isinstance(row, Mapping),
                        f"alpha frontier {key} row is invalid")
                ordinal_value = row.get("ordinal")
                module_value = row.get("module")
                if ordinal_value is None:
                    continue
                require(
                    isinstance(ordinal_value, int)
                    and not isinstance(ordinal_value, bool)
                    and 1 <= ordinal_value <= end_ordinal,
                    "alpha frontier module override ordinal is invalid",
                )
                require(
                    isinstance(module_value, str)
                    and MODULE_RE.fullmatch(module_value) is not None,
                    "alpha frontier module override name is invalid",
                )
                prior = overrides.get(ordinal_value)
                require(prior is None or prior == module_value,
                        "conflicting recursive alpha module overrides")
                overrides[ordinal_value] = module_value

                output_value = row.get("outputPath") or row.get("oleanPath")
                output_hash = row.get("outputSha256") or row.get("oleanSha256")
                # Legacy ancestry rows sometimes name a source module without
                # publishing an olean hash.  They cannot authorize a changed
                # import, so ignore the incomplete output here; the final
                # changed-import gate below still requires a complete contract.
                if output_value is None or output_hash is None:
                    continue
                output = _workspace_resource_path(str(output_value))
                digest = normalized_sha256(str(output_hash),
                                           "alpha module output hash")
                require_file_hash(output, digest, "accepted alpha module output")
                require(output.name == f"{module_value.split('.')[-1]}.olean",
                        "alpha module output filename changed")
                contract = (output, digest)
                prior_output = outputs.get(module_value)
                require(prior_output is None or prior_output == contract,
                        "conflicting recursive alpha module outputs")
                outputs[module_value] = contract

        parent = data.get("parent")
        if not isinstance(parent, Mapping):
            return
        parent_name = parent.get("resource") or parent.get("resourcePath")
        parent_hash = parent.get("resourceSha256")
        if parent_name is None and parent_hash is None:
            return
        require(parent_name is not None and parent_hash is not None,
                "alpha frontier parent provenance is incomplete")
        visit(
            _workspace_resource_path(str(parent_name)),
            normalized_sha256(str(parent_hash), "alpha parent resource hash"),
        )

    visit(resource.resolve(), normalized_sha256(
        expected_sha256, "accepted alpha resource hash"
    ))
    changed = 0
    for ordinal, module in sorted(overrides.items()):
        if imports[ordinal - 1] == module:
            continue
        require(module in outputs,
                "recursive alpha override lacks an accepted module output")
        output, digest = outputs[module]
        candidates = [
            root / f"{module}.olean" for root in roots
            if (root / f"{module}.olean").is_file()
        ]
        require(output in candidates,
                "alpha override is absent from the accepted LEAN_PATH roots")
        require(sha256(output) == digest,
                "alpha override output changed after ancestry validation")
        imports[ordinal - 1] = module
        changed += 1

    frontier.imports = tuple(imports)
    frontier.recursive_override_contract_verified = True
    frontier.recursive_override_count = len(overrides)
    frontier.recursive_override_changed_count = changed


def load_alpha_frontier(
    backend: SimpleNamespace, resource: Path, expected_sha256: str
) -> tuple[Any, dict[str, Any]]:
    resource = resource.resolve()
    require_file_hash(resource, expected_sha256, "accepted alpha resource")
    data = json.loads(resource.read_text(encoding="utf-8"))
    require(isinstance(data, dict), "accepted alpha resource is not a JSON object")
    status = str(data.get("status", ""))
    prefix = data.get("firstUsePrefix")
    require(status.startswith("PASS_KERNEL_FIRST_USE_PREFIX_")
            and isinstance(prefix, Mapping),
            "alpha resource is not an accepted first-use kernel frontier")
    require(data.get("trust") == 0,
            "alpha frontier was not accepted at Lean trust level zero")
    end_ordinal = prefix.get("endOrdinal")
    require(isinstance(end_ordinal, int) and end_ordinal >= 1,
            "alpha frontier has no positive end ordinal")
    require(exact_three_alpha_resource(data),
            "alpha frontier lacks an exact-three axiom audit")
    frontier = backend.alpha_core.AlphaFrontier.load(
        resource, expected_sha256, end_ordinal
    )
    require(frontier.end_ordinal == end_ordinal,
            "loaded alpha frontier ordinal changed")
    reconcile_recursive_alpha_imports(frontier, resource, expected_sha256)
    return frontier, data


def build_emitter_class(backend: SimpleNamespace) -> type:
    nominal = backend.nominal
    structural = backend.structural
    compact_fv = backend.compact_fv
    wpp_base = backend.wpp_base
    fv_v1 = backend.fv_v1

    compact_fv.verify_host_class(
        structural.WPPCompactEmitterExactRepeatedRootFV
    )

    class ParameterizedNominalStructuralEmitter(
        compact_fv.CompactFVNormalizeMixin,
        nominal.NominalEmitter,
        structural.WPPCompactEmitterExactRepeatedRootFV,
    ):
        """Runtime nominal/v5 algebra plus compact FV normalization."""

        compact_fv_error_type = backend.MMError

        def __init__(
            self,
            database: Any,
            replayer: Any,
            endpoint: str,
            frontier: Any,
            source_sha256: str,
        ) -> None:
            # This is the accepted WPP constructor with its global ENDPOINT
            # replaced by the validated CLI endpoint.
            self.database = database
            self.replayer = replayer
            self.endpoint = endpoint
            self.alpha_frontier = frontier
            self.rules = wpp_base.extract_rules(database, replayer, endpoint)
            self.rule_by_label = {rule.label: rule for rule in self.rules}
            self.rule_by_head = {
                (rule.target_sort, rule.target_head): rule for rule in self.rules
            }
            self.defined_heads = set(self.rule_by_head)
            choice = wpp_base.choice_replay
            self.recanon_expander = choice.ProvenanceBlindExpander(self.rules)
            self.recanon_certificate = choice.RecanonCertificateEmitter()

            dispatch_data = json.loads(choice.DISPATCH.read_text(encoding="utf-8"))
            self.dispatch = {
                entry["label"]: entry for entry in dispatch_data["entries"]
            }
            for rule in self.rules:
                if rule.label not in self.dispatch:
                    self.dispatch[rule.label] = {
                        "label": rule.label,
                        "category": wpp_base.definition_category(rule, replayer),
                        "target_head": rule.target_head,
                        "dummy_count": len(rule.dummy_variables),
                    }

            exact_data = json.loads(choice.EXACT_DF_CALLS.read_text(encoding="utf-8"))
            self.exact_df_calls = {
                entry["label"]: entry for entry in exact_data["calls"]
            }
            for alpha_manifest in choice.ALPHA_CALL_MANIFESTS:
                alpha_data = json.loads(alpha_manifest.read_text(encoding="utf-8"))
                self.exact_df_calls.update(
                    {entry["label"]: entry for entry in alpha_data["records"]}
                )

            self.wpp_leaf_modules: list[str] = []
            self.wpp_leaf_manifests: list[dict[str, str]] = []
            self.reused_entries: dict[str, dict[str, object]] = {}
            self.trace: list[dict[str, object]] = []
            self.cache_dv_labels: set[str] = set()
            self._dv_cache: dict[str, tuple[str, str]] | None = None
            self._current_theorem = None
            self._current_local_sorts: dict[str, str] = {}
            self.symbolic_fv = choice.SymbolicFV(self.rules)
            for rule in self.rules:
                dummy_names = {name for _sort, name in rule.dummy_variables}
                template = self.symbolic_fv.of(rule.rhs, dummy_names)
                self.symbolic_fv.templates[rule.target_head] = template

            # Install the accepted WPP-only FV head registry.  The manifest is
            # globally complete (143 heads), but a smaller endpoint closure may
            # legitimately use only a subset.
            manifest_path = backend.wpp_config.WPP_FV_MANIFEST
            manifest_pin = backend.wpp_config.WPP_FV_MANIFEST_SHA256
            require_file_hash(manifest_path, manifest_pin, "WPP FV manifest")
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            require(
                manifest.get("status") == "GENERATED_UNCHECKED"
                and manifest.get("namespace")
                == "NFChoice.Compiler.WPPCompactSyntaxFVExplicit"
                and manifest.get("definition_count") == 143
                and manifest.get("source_sha256") == source_sha256,
                "source is not covered by the accepted WPP FV profile",
            )
            label_to_lemma = manifest.get("label_to_lemma")
            require(isinstance(label_to_lemma, dict) and len(label_to_lemma) == 143,
                    "accepted WPP FV manifest is incomplete")
            self.wpp_fv_lemma_by_head: dict[tuple[str, str], str] = {}
            self.wpp_fv_lemma_rewrite: dict[str, str] = {}
            for label, value in label_to_lemma.items():
                rule = self.rule_by_label.get(str(label))
                if rule is None:
                    continue
                lemma = str(value)
                expected_suffix = f".fv_syn_{choice.safe(rule.target_head)}"
                require(lemma.endswith(expected_suffix),
                        f"WPP FV lemma/head mismatch: {label}: {lemma}")
                key = (rule.target_sort, rule.target_head)
                require(key not in self.wpp_fv_lemma_by_head,
                        f"duplicate WPP FV target head: {key}")
                self.wpp_fv_lemma_by_head[key] = lemma
                old = (
                    "NFChoice.Compiler.CompactSyntaxFVExplicit."
                    f"fv_syn_{choice.safe(rule.target_head)}"
                )
                self.wpp_fv_lemma_rewrite[old] = lemma

        def definition_leaf(self, label, subst, essentials, result):  # type: ignore[no-untyped-def]
            accepted = self.alpha_frontier.definition_leaf_call(
                self, label, subst, essentials
            )
            if accepted is not None:
                return accepted
            return nominal.NominalEmitter.definition_leaf(
                self, label, subst, essentials, result
            )

        def emit_theorem(self, label, available):  # type: ignore[no-untyped-def]
            self.cache_dv_labels.add(label)
            return super().emit_theorem(label, available)

    return ParameterizedNominalStructuralEmitter


def alpha_ordinal_map(backend: SimpleNamespace) -> dict[str, int]:
    global_records = getattr(backend.alpha_core, "GLOBAL_RECORDS", None)
    if global_records is not None:
        return {
            str(row["label"]): ordinal
            for ordinal, row in enumerate(global_records, start=1)
        }
    manifest = json.loads(
        backend.alpha_core.MANIFEST.read_text(encoding="utf-8")
    )
    result: dict[str, int] = {}
    for row in manifest.get("records", []):
        if row.get("surface") == "base":
            result[str(row["label"])] = int(row["surface_ordinal"])
    return result


def scan_leaf_coverage(
    backend: SimpleNamespace,
    emitter: Any,
    database: Any,
    theorem_labels: Sequence[str],
    frontier: Any,
) -> list[dict[str, object]]:
    supported_special_definitions = {
        "df-eu", "df-nfc", "df-clab", "df-cleq", "df-clel", "df-tru"
    }
    supported_literal = (
        set(backend.nominal.base.LOGICAL)
        | set(backend.nominal.NOMINAL_LITERAL_AXIOMS)
    )
    ordinals = alpha_ordinal_map(backend)
    accepted_alpha = set(frontier.labels)
    missing: list[dict[str, object]] = []
    seen: set[str] = set()
    for theorem_label in theorem_labels:
        theorem = database.statements[theorem_label]
        for op in theorem.proof_ops:
            if op.kind != "label":
                continue
            reference = str(op.value)
            rule = database.statements[reference]
            if rule.kind != "$a" or rule.typecode != "|-":
                continue
            if reference in supported_literal or reference in accepted_alpha:
                continue
            category: str | None = None
            supported = False
            if reference.startswith("df-"):
                entry = emitter.dispatch.get(reference)
                category = str(entry.get("category")) if entry else None
                supported = (
                    reference in supported_special_definitions
                    or category in {"exact_biimp", "exact_classEq"}
                )
            if supported or reference in seen:
                continue
            seen.add(reference)
            missing.append(
                {
                    "theorem": theorem_label,
                    "label": reference,
                    "category": category or "literal",
                    "alphaOrdinal": ordinals.get(reference),
                }
            )
    return missing


def proof_ops_digest(statement: Any) -> str:
    payload = "\n".join(
        f"{op.kind}:{op.value}" for op in statement.proof_ops
    ).encode("utf-8")
    return sha256_bytes(payload)


def cache_census(block: bytes) -> dict[str, int]:
    result = {"total": 0, "nonmembership": 0, "inequality": 0, "disjoint": 0}
    for match in DV_CACHE_RE.finditer(block):
        target = match.group(2)
        result["total"] += 1
        if b"Disjoint" in target:
            result["disjoint"] += 1
        elif b"\xe2\x88\x89" in target:
            result["nonmembership"] += 1
        elif b"\xe2\x89\xa0" in target:
            result["inequality"] += 1
    return result


@dataclass(frozen=True)
class Emission:
    blocks: tuple[bytes, ...]
    theorem_records: tuple[dict[str, object], ...]
    trace: tuple[dict[str, object], ...]
    cache_census: dict[str, int]
    compact_fv_normalization_count: int
    generic_dv_fallback_count: int


def emit_selection(
    emitter: Any,
    database: Any,
    selection: Selection,
) -> Emission:
    available = set(selection.earlier_labels)
    blocks: list[bytes] = []
    theorem_records: list[dict[str, object]] = []
    aggregate_cache = {
        "total": 0, "nonmembership": 0, "inequality": 0, "disjoint": 0
    }
    compact_fv_count = 0
    generic_count = 0
    for offset, label in enumerate(selection.selected_labels):
        before = len(emitter.trace)
        text = emitter.emit_theorem(label, frozenset(available))
        available.add(label)
        expected_header = f"noncomputable def g_{safe(label)}"
        require(text.startswith(expected_header),
                f"unexpected emitted theorem header for {label}")
        block = text.encode("utf-8") + b"\n\n"
        require(FORBIDDEN_SOURCE_RE.search(block) is None,
                f"forbidden Lean token emitted in {label}")
        theorem_generic = len(GENERIC_DV_FALLBACK_RE.findall(block))
        require(theorem_generic == 0,
                f"generic DV fallback survived structural compilation in {label}")
        generic_count += theorem_generic
        census = cache_census(block)
        theorem_compact_fv_count = block.count(
            b"have compact_fv_not_mem_empty"
        )
        require(
            theorem_compact_fv_count == census["nonmembership"],
            "nonmembership cache escaped compact FV normalization in "
            f"{label}: {theorem_compact_fv_count} != {census['nonmembership']}",
        )
        compact_fv_count += theorem_compact_fv_count
        for key in aggregate_cache:
            aggregate_cache[key] += census[key]
        trace = emitter.trace[before:]
        statement = database.statements[label]
        theorem_records.append(
            {
                "ordinal": selection.start_ordinal + offset,
                "label": label,
                "safeName": safe(label),
                "proofOpCount": len(statement.proof_ops),
                "proofOpsSha256": proof_ops_digest(statement),
                "applicationCount": len(trace),
                "applicationTraceSha256": canonical_json_sha256(trace),
                "emittedBytes": len(block),
                "emittedSha256": sha256_bytes(block),
                "structuralCertificateCensus": census,
                "compactFvNormalizationCount": theorem_compact_fv_count,
            }
        )
        blocks.append(block)
    return Emission(
        tuple(blocks),
        tuple(theorem_records),
        tuple(emitter.trace),
        aggregate_cache,
        compact_fv_count,
        generic_count,
    )


def lean_header(
    imports: Sequence[str], namespace: str
) -> bytes:
    import_text = "".join(f"import {module}\n" for module in unique(imports))
    return f"""{import_text}
set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace {namespace}

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

""".encode("utf-8")


def lean_footer(last_label: str, namespace: str) -> bytes:
    return (
        f"#print axioms g_{safe(last_label)}\n\n"
        f"end {namespace}\n"
    ).encode("utf-8")


def derived_module_prefix(endpoint: str, start: int, end: int) -> str:
    result = f"NominalMMReplay_{safe(endpoint)}_{start:04d}_{end:04d}"
    require(LEAN_IDENT_RE.fullmatch(result) is not None,
            "derived module prefix is not a Lean identifier")
    return result


def build_source_artifacts(
    emission: Emission,
    selection: Selection,
    frontier: Any,
    module_prefix: str,
    namespace: str,
    split_bytes: int,
    predecessor: PredecessorContract | None,
    output: Path,
) -> tuple[list[dict[str, object]], dict[str, object], dict[Path, bytes]]:
    groups = group_blocks(emission.blocks, split_bytes)
    support_imports = unique(
        (
            "WPPCompactSourceSyntax",
            "WPPCompactSyntaxFVExplicit",
            "CompactSyntaxFV",
            "CoreFVSimp",
            "NominalSubstitutionLemmas",
            "NominalDefinitionRefl",
            *frontier.imports,
            *WPP_SUPPORT_IMPORTS[6:],
        )
    )
    files: dict[Path, bytes] = {}
    parts: list[dict[str, object]] = []
    reconstructed: list[bytes] = []
    for part_index, (begin, end) in enumerate(groups, start=1):
        module = f"{module_prefix}Part{part_index:03d}"
        prior_module = (
            predecessor.module
            if part_index == 1 and predecessor is not None
            else None
            if part_index == 1
            else f"{module_prefix}Part{part_index - 1:03d}"
        )
        imports = list(support_imports)
        if prior_module is not None:
            imports.append(prior_module)
        copied = b"".join(emission.blocks[begin:end])
        oversized = len(copied) > split_bytes
        require(not oversized or end - begin == 1,
                f"oversized non-singleton part: {module}")
        source = (
            lean_header(imports, namespace)
            + copied
            + lean_footer(selection.selected_labels[end - 1], namespace)
        )
        require(FORBIDDEN_SOURCE_RE.search(source) is None,
                f"forbidden token in generated module {module}")
        require(GENERIC_DV_FALLBACK_RE.search(source) is None,
                f"generic DV fallback in generated module {module}")
        path = output / f"{module}.lean"
        files[path] = source
        reconstructed.extend(emission.blocks[begin:end])
        parts.append(
            {
                "part": part_index,
                "module": module,
                "predecessor": prior_module,
                "startTheoremOrdinal": selection.start_ordinal + begin,
                "endTheoremOrdinal": selection.start_ordinal + end - 1,
                "firstLabel": selection.selected_labels[begin],
                "lastLabel": selection.selected_labels[end - 1],
                "theoremCount": end - begin,
                "copiedTheoremBytes": len(copied),
                "copiedTheoremSha256": sha256_bytes(copied),
                "oversizedSingleton": oversized,
                "source": str(path),
                "sourceBytes": len(source),
                "sourceSha256": sha256_bytes(source),
            }
        )
    require(tuple(reconstructed) == emission.blocks,
            "part sequence does not reconstruct emitted theorem blocks")

    last_module = str(parts[-1]["module"])
    umbrella_path = output / f"{module_prefix}.lean"
    umbrella = (
        f"import {last_module}\n\n"
        f"namespace {namespace}\n\n"
        f"#print axioms g_{safe(selection.selected_labels[-1])}\n\n"
        f"end {namespace}\n"
    ).encode("utf-8")
    files[umbrella_path] = umbrella
    umbrella_record = {
        "module": module_prefix,
        "imports": last_module,
        "endpoint": f"g_{safe(selection.selected_labels[-1])}",
        "source": str(umbrella_path),
        "sourceBytes": len(umbrella),
        "sourceSha256": sha256_bytes(umbrella),
    }
    return parts, umbrella_record, files


def validate_args(args: argparse.Namespace) -> argparse.Namespace:
    args.source = args.source.resolve()
    args.alpha_frontier_resource = args.alpha_frontier_resource.resolve()
    args.output_dir = args.output_dir.resolve()
    args.source_sha256 = normalized_sha256(args.source_sha256, "source")
    args.alpha_frontier_sha256 = normalized_sha256(
        args.alpha_frontier_sha256, "alpha frontier"
    )
    require(args.split_bytes > 0, "--split-bytes must be positive")
    require(bool(args.endpoint), "--endpoint must be nonempty")
    require((args.start_ordinal is None) == (args.end_ordinal is None),
            "--start-ordinal and --end-ordinal must be supplied together")
    predecessor_args = (
        args.predecessor_resource is not None,
        args.predecessor_resource_sha256 is not None,
    )
    require(predecessor_args[0] == predecessor_args[1],
            "predecessor resource path/hash must be supplied together")
    if args.predecessor_resource is not None:
        args.predecessor_resource = args.predecessor_resource.resolve()
        args.predecessor_resource_sha256 = normalized_sha256(
            args.predecessor_resource_sha256, "predecessor resource"
        )
    if args.module_prefix is not None:
        require(LEAN_IDENT_RE.fullmatch(args.module_prefix) is not None,
                f"invalid Lean module prefix: {args.module_prefix!r}")
    args.namespace = require_module_name(args.namespace, "namespace")
    require(args.output_dir.parent.is_dir(),
            f"output parent directory does not exist: {args.output_dir.parent}")
    require(not args.output_dir.exists(),
            f"refusing to overwrite append-only output: {args.output_dir}")
    staging = args.output_dir.parent / f".{args.output_dir.name}.staging-v1"
    require(not staging.exists(), f"stale fail-closed staging directory: {staging}")
    args.staging_dir = staging
    return args


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Source-only checked Metamath -> nominal Lean replay translator; "
            "does not invoke Lean"
        )
    )
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--source-sha256", required=True)
    parser.add_argument("--endpoint", required=True)
    parser.add_argument("--start-ordinal", type=int)
    parser.add_argument("--end-ordinal", type=int)
    parser.add_argument("--alpha-frontier-resource", type=Path, required=True)
    parser.add_argument("--alpha-frontier-sha256", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--split-bytes", type=int, required=True)
    parser.add_argument("--predecessor-resource", type=Path)
    parser.add_argument("--predecessor-resource-sha256")
    parser.add_argument("--module-prefix")
    parser.add_argument("--namespace", default=DEFAULT_NAMESPACE)
    parser.add_argument(
        "--wpp-profile",
        choices=WPP_PROFILE_IDS,
        default=DEFAULT_WPP_PROFILE,
        help=(
            "frozen source-only backend profile (default: WPP_PROFILE_V2; "
            "V1 remains available for exact legacy replay)"
        ),
    )
    parser.add_argument(
        "--audit-only",
        action="store_true",
        help="publish the full source/closure/frontier/coverage preflight without Lean emission",
    )
    return parser


def publish(staging: Path, output: Path, files: Mapping[Path, bytes]) -> None:
    staging.mkdir(parents=False)
    for final_path, content in files.items():
        relative = final_path.relative_to(output)
        target = staging / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
        require(sha256(target) == sha256_bytes(content),
                f"staged output hash mismatch: {target}")
    require(not output.exists(), f"append-only output appeared during run: {output}")
    os.replace(staging, output)


def main(argv: Sequence[str] | None = None) -> int:
    args = validate_args(make_parser().parse_args(argv))
    sys.setrecursionlimit(200_000)
    require_file_hash(args.source, args.source_sha256, "Metamath source")

    profile = load_wpp_profile(args.wpp_profile)
    backend = load_backend(args.wpp_profile)
    profile_record = wpp_profile_provenance(profile)
    backend.wpp_config.verify_surface_inputs()
    require_file_hash(
        backend.wpp_config.WPP_SOURCE_AUDIT,
        backend.wpp_config.WPP_SOURCE_AUDIT_SHA256,
        "accepted WPP source audit",
    )
    frontier, alpha_data = load_alpha_frontier(
        backend, args.alpha_frontier_resource, args.alpha_frontier_sha256
    )

    require_no_metamath_includes(
        backend.tokenize_text(args.source.read_text(encoding="utf-8"))
    )
    database = backend.Database()
    database.parse(args.source)
    require(args.endpoint in database.statements,
            f"unknown endpoint label: {args.endpoint}")
    endpoint_statement = database.statements[args.endpoint]
    require(endpoint_statement.kind == "$p" and endpoint_statement.typecode == "|-",
            "endpoint must be a proved |- statement")
    replayer = backend.ASTReplayer(database, backend.Grammar(database))
    replay_audit = replayer.replay_closure(args.endpoint)
    closure = database.dependency_closure(args.endpoint)
    theorem_labels = tuple(
        statement.label for statement in closure
        if statement.kind == "$p" and statement.typecode == "|-"
    )
    require(len(set(safe(label) for label in theorem_labels)) == len(theorem_labels),
            "safe Lean theorem names collide in endpoint closure")
    selection = select_interval(
        theorem_labels, args.start_ordinal, args.end_ordinal
    )

    predecessor: PredecessorContract | None = None
    if selection.start_ordinal > 1:
        require(args.predecessor_resource is not None,
                "a partial ordinal interval requires --predecessor-resource and hash")
        predecessor = load_predecessor(
            args.predecessor_resource,
            args.predecessor_resource_sha256,
            args.source_sha256,
            args.endpoint,
            selection.start_ordinal - 1,
        )
    else:
        require(args.predecessor_resource is None,
                "a full-prefix interval starting at one must not name a predecessor")

    emitter_class = build_emitter_class(backend)
    emitter = emitter_class(
        database, replayer, args.endpoint, frontier, args.source_sha256
    )
    missing = scan_leaf_coverage(
        backend, emitter, database, selection.selected_labels, frontier
    )
    require_supported_leaf_coverage(missing)

    module_prefix = args.module_prefix or derived_module_prefix(
        args.endpoint, selection.start_ordinal, selection.end_ordinal
    )
    require(LEAN_IDENT_RE.fullmatch(module_prefix) is not None,
            "module prefix is not a Lean identifier")
    producer = {"path": str(THIS), "sha256": sha256(THIS)}
    closure_proof_hashes = {
        label: proof_ops_digest(database.statements[label])
        for label in selection.selected_labels
    }
    base_audit: dict[str, object] = {
        "schema": "nf-reusable-nominal-mm-translator-source-audit-v1",
        "status": (
            "PASS_SOURCE_ONLY_PREFLIGHT" if args.audit_only
            else "PASS_SOURCE_ONLY_EMITTED_STRUCTURAL"
        ),
        "leanStartedByThisProducer": False,
        "producer": producer,
        "backendPins": {
            str(path): digest for path, digest in BACKEND_PINS.items()
        },
        "wppProfile": profile_record,
        "compactFvNormalizationBackend": backend.compact_fv.provenance(),
        "source": str(args.source),
        "sourceSha256": args.source_sha256,
        "endpoint": args.endpoint,
        "endpointAst": replay_audit.endpoint_ast.sexpr(),
        "closureAssertionCount": replay_audit.assertion_count,
        "closureProofTheoremCount": len(theorem_labels),
        "startTheoremOrdinal": selection.start_ordinal,
        "endTheoremOrdinal": selection.end_ordinal,
        "selectedTheoremCount": len(selection.selected_labels),
        "selectedLabels": selection.selected_labels,
        "selectedProofOpsSha256": closure_proof_hashes,
        "selectedProofOpsMapSha256": canonical_json_sha256(closure_proof_hashes),
        "alphaFrontier": {
            "resource": str(args.alpha_frontier_resource),
            "resourceSha256": args.alpha_frontier_sha256,
            "endOrdinal": frontier.end_ordinal,
            "imports": frontier.imports,
            "oleanRoots": tuple(str(path) for path in frontier.olean_roots),
            "status": alpha_data["status"],
            "recursiveOverrideContractVerified": getattr(
                frontier, "recursive_override_contract_verified", False
            ),
            "recursiveOverrideCount": getattr(
                frontier, "recursive_override_count", 0
            ),
            "recursiveOverrideChangedCount": getattr(
                frontier, "recursive_override_changed_count", 0
            ),
        },
        "predecessor": None if predecessor is None else {
            "resource": str(predecessor.resource),
            "resourceSha256": predecessor.resource_sha256,
            "status": predecessor.status,
            "module": predecessor.module,
            "endTheoremOrdinal": predecessor.end_theorem_ordinal,
            "boundaryKind": predecessor.boundary_kind,
            "sourceResource": str(predecessor.source_resource),
            "sourceResourceSha256": predecessor.source_resource_sha256,
            "sourceArtifact": str(predecessor.source_artifact),
            "sourceArtifactSha256": predecessor.source_artifact_sha256,
            "kernelArtifact": (
                None if predecessor.kernel_artifact is None else {
                    "path": str(predecessor.kernel_artifact),
                    "sha256": predecessor.kernel_artifact_sha256,
                }
            ),
        },
        "coverage": {
            "unsupportedLeaves": missing,
            "allSelectedLeavesCovered": not missing,
        },
        "checks": {
            "metamathProofsVerified": True,
            "endpointAstReplayed": True,
            "ordinalIntervalContiguous": True,
            "acceptedAlphaExactThree": True,
            "wppProfileVerifiedBeforeBackendImport": True,
            "backendImportsForcedFromVerifiedSource": True,
            "outputAppendOnly": True,
            "leanNotStarted": True,
        },
    }

    files: dict[Path, bytes] = {}
    resource: dict[str, object]
    if args.audit_only:
        resource = {
            "schema": "nf-reusable-nominal-mm-translator-v1",
            "status": "PASS_SOURCE_ONLY_PREFLIGHT",
            "mode": "audit-only",
            "sourceAudit": base_audit,
            "wppProfile": profile_record,
            "settings": {
                "modulePrefix": module_prefix,
                "namespace": args.namespace,
                "splitBytes": args.split_bytes,
            },
        }
        resource_path = args.output_dir / "resource.json"
        files[resource_path] = json_bytes(resource)
    else:
        emission = emit_selection(emitter, database, selection)
        parts, umbrella, source_files = build_source_artifacts(
            emission,
            selection,
            frontier,
            module_prefix,
            args.namespace,
            args.split_bytes,
            predecessor,
            args.output_dir,
        )
        files.update(source_files)
        aggregate = b"".join(emission.blocks)
        base_audit.update(
            {
                "aggregateTheoremBytes": len(aggregate),
                "aggregateTheoremSha256": sha256_bytes(aggregate),
                "applicationCount": len(emission.trace),
                "applicationTraceSha256": canonical_json_sha256(emission.trace),
                "structuralCertificateCensus": emission.cache_census,
                "compactFvNormalizationCount":
                    emission.compact_fv_normalization_count,
                "genericDvFallbackCount": emission.generic_dv_fallback_count,
                "theorems": emission.theorem_records,
            }
        )
        checks = base_audit["checks"]
        assert isinstance(checks, dict)
        checks.update(
            {
                "allTheoremBodiesPartitionedByteExactly": True,
                "allNonSingletonPartsWithinByteLimit": True,
                "allOversizedPartsAreSingletons": True,
                "genericDvFallbackCountZero":
                    emission.generic_dv_fallback_count == 0,
                "allNonmembershipCachesCompactNormalized":
                    emission.compact_fv_normalization_count
                    == emission.cache_census["nonmembership"],
                "forbiddenGeneratedTokensAbsent": True,
            }
        )
        audit_path = args.output_dir / "source_audit.json"
        audit_content = json_bytes(base_audit)
        files[audit_path] = audit_content
        resource = {
            "schema": "nf-reusable-nominal-mm-translator-v1",
            "status": "PASS_SOURCE_ONLY_EMITTED_STRUCTURAL",
            "leanStartedByThisProducer": False,
            "producer": producer,
            "source": str(args.source),
            "sourceSha256": args.source_sha256,
            "endpoint": args.endpoint,
            "endpointAst": replay_audit.endpoint_ast.sexpr(),
            "closureProofTheoremCount": len(theorem_labels),
            "startTheoremOrdinal": selection.start_ordinal,
            "endTheoremOrdinal": selection.end_ordinal,
            "theoremCount": len(selection.selected_labels),
            "maximumCopiedTheoremBytes": args.split_bytes,
            "partCount": len(parts),
            "parts": parts,
            "umbrellaModule": umbrella,
            "aggregateTheoremBytes": len(aggregate),
            "aggregateTheoremSha256": sha256_bytes(aggregate),
            "applicationCount": len(emission.trace),
            "applicationTraceSha256": canonical_json_sha256(emission.trace),
            "structuralCertificateCensus": emission.cache_census,
            "compactFvNormalizationCount":
                emission.compact_fv_normalization_count,
            "compactFvNormalizationBackend":
                backend.compact_fv.provenance(),
            "wppProfile": profile_record,
            "genericDvFallbackCount": emission.generic_dv_fallback_count,
            "sourceAudit": {
                "path": str(audit_path),
                "sha256": sha256_bytes(audit_content),
            },
            "alphaFrontier": base_audit["alphaFrontier"],
            "predecessor": base_audit["predecessor"],
            "forbiddenGeneratedSourceTokens": [],
        }
        resource_path = args.output_dir / "resource.json"
        files[resource_path] = json_bytes(resource)

    publish(args.staging_dir, args.output_dir, files)
    final_resource = args.output_dir / "resource.json"
    print(json.dumps({
        "status": resource["status"],
        "output": str(args.output_dir),
        "resource": str(final_resource),
        "resourceSha256": sha256(final_resource),
        "leanStarted": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
