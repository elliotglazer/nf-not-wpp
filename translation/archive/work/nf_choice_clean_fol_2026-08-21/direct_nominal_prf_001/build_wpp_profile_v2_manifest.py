#!/usr/bin/env python3
"""Build the immutable ``WPP_PROFILE_V2`` source-only input manifest.

V2 is a strict append-only extension of the audited V1 file inventory.  It
adds the global nominal-alpha v3 dispatcher and the three accepted a4972
metadata documents which bind B49..B71,W1 through global ordinal 72.  It does
not invoke Lean and deliberately does not inventory the generated Lean source
files: their ordered hashes and exact-statement audit are frozen by the a4972
metadata documents included here.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
THIS = Path(__file__).resolve()
V1 = HERE / "WPP_PROFILE_V1.json"
OUT = HERE / "WPP_PROFILE_V2.json"
CORE_V3 = HERE / "nominal_alpha_dispatch_core_v3.py"
A4972_MANIFEST = (
    HERE / "a4972s1" / "NominalAlphaGlobalPrefix072Structural001.json"
)
A4972_AUDIT = HERE / "a4972s1a1" / "resource.json"
A4972_JOIN_AUDIT = (
    HERE / "nominal_alpha_v3_a4972_join_source_audit_001" / "resource.json"
)

V1_SHA256 = "2DC43D9E4C07BE4B712DF4858D4EEFD16FC8D9861B093E7CDDF02EDDFEB2D2D2"
CORE_V3_SHA256 = "4B05500EEBD44F4605DF67E5CBEFF64DC92F28C3D6B3434E4A2FA6BCB04C6C58"
A4972_MANIFEST_SHA256 = (
    "8F55E7A661F33BD4E6ECAE257FCEB314CB7B31113D164681E3FAC192764F7FD5"
)
A4972_AUDIT_SHA256 = (
    "D5B29D8E5BF1B2072924A6B30D97B673CD218A03193C268701C45D2B9C3B5A08"
)
A4972_JOIN_AUDIT_SHA256 = (
    "4A93CA905E684D3E1740D9834744E64B3742711876A3661583E6360A5251A875"
)

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


def canonical_sha256(value: object) -> str:
    return sha256_bytes(
        json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ).encode("utf-8")
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def relative(path: Path) -> str:
    path = path.resolve()
    require(path.is_relative_to(WORKSPACE), f"profile input escapes workspace: {path}")
    return path.relative_to(WORKSPACE).as_posix()


def checked_json(path: Path, expected_sha256: str) -> dict[str, Any]:
    require(path.is_file(), f"missing V2 input: {path}")
    require(sha256(path) == expected_sha256, f"V2 input identity changed: {path}")
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"V2 JSON input is not an object: {path}")
    return value


def main() -> int:
    v1 = checked_json(V1, V1_SHA256)
    require(
        v1.get("profileId") == "WPP_PROFILE_V1"
        and v1.get("profileVersion") == 1
        and v1.get("inputCount") == 92
        and v1.get("pythonModuleCount") == 19
        and v1.get("fixedDataCount") == 73,
        "pinned WPP_PROFILE_V1 contract changed",
    )
    require(sha256(CORE_V3) == CORE_V3_SHA256, "nominal-alpha core v3 changed")

    source = checked_json(A4972_MANIFEST, A4972_MANIFEST_SHA256)
    audit = checked_json(A4972_AUDIT, A4972_AUDIT_SHA256)
    join = checked_json(A4972_JOIN_AUDIT, A4972_JOIN_AUDIT_SHA256)
    require(
        source.get("schema")
        == "nf-wpp-nominal-alpha-global-successor-049-072-v1"
        and source.get("status") == "GENERATED_SOURCE_ONLY_KERNEL_PENDING"
        and source.get("leanStartedByProducer") is False
        and source.get("firstGlobalOrdinal") == 49
        and source.get("lastGlobalOrdinal") == 72
        and source.get("count") == 24
        and source.get("surfaceSequence") == "B49..B71,W1"
        and source.get("globalRecordContract") == GLOBAL_PREFIX72_CONTRACT,
        "a4972 source manifest contract changed",
    )
    require(
        audit.get("schema")
        == "nf-wpp-nominal-alpha-global-049-072-source-audit-v1"
        and audit.get("status") == "PASS_SOURCE_AUTHORIZED_KERNEL_PENDING"
        and audit.get("leanStartedByAudit") is False
        and audit.get("kernelAcceptanceClaimed") is False
        and audit.get("manifest", {}).get("sha256") == A4972_MANIFEST_SHA256
        and audit.get("globalPrefix72", {}).get("recordContract")
        == GLOBAL_PREFIX72_CONTRACT,
        "a4972 source audit contract changed",
    )
    successor = join.get("successor", {})
    w1 = successor.get("w1Identity", {}) if isinstance(successor, dict) else {}
    require(
        join.get("schema")
        == "nf-wpp-nominal-alpha-v3-a4972-independent-source-join-v1"
        and join.get("status")
        == "PASS_SOURCE_ONLY_PREFIX48_COMPAT_GLOBAL49_72_EXACT_KERNEL_PENDING"
        and join.get("leanStartedByThisAudit") is False
        and join.get("kernelAcceptanceClaimed") is False
        and successor.get("count") == 24
        and successor.get("firstGlobalOrdinal") == 49
        and successor.get("lastGlobalOrdinal") == 72
        and successor.get("surfaceSequence") == "B49..B71,W1"
        and successor.get("sourceHashOrderSha256")
        == "F5A3BAD8C928365ACB77E6C442AD7063DE80DDBC0D95B47DC83FA9980302C854"
        and successor.get("importCount") == 72
        and successor.get("importChainSha256")
        == "157CF0DDB86EBDA8C4EE88973F45616639B890BFAC6C1E8D56521DD268CA192E"
        and w1.get("globalOrdinal") == 72
        and w1.get("surface") == "wpp"
        and w1.get("surfaceOrdinal") == 1
        and w1.get("label") == "df-iso"
        and w1.get("originalSourceByteIdentical") is True,
        "independent a4972 join contract changed",
    )

    inputs = [dict(entry) for entry in v1["inputs"]]

    def add(
        identifier: str,
        path: Path,
        kind: str,
        phase: str,
        read_by: str,
        *,
        module: str | None = None,
    ) -> None:
        path = path.resolve()
        require(path.is_file(), f"missing V2 input: {path}")
        require(
            all(entry["path"] != relative(path) for entry in inputs),
            f"duplicate V2 input path: {path}",
        )
        entry: dict[str, Any] = {
            "id": identifier,
            "root": "workspace",
            "path": relative(path),
            "kind": kind,
            "phases": [phase],
            "readBy": [read_by],
            "bytes": path.stat().st_size,
            "sha256": sha256(path),
        }
        if module is not None:
            entry["module"] = module
        inputs.append(entry)

    add(
        "profile:WPP_PROFILE_V1",
        V1,
        "json-parent-profile-manifest",
        "profile-preflight",
        "WPP_PROFILE_V2 immutable-parent check",
    )
    add(
        "python:nominal_alpha_dispatch_core_v3",
        CORE_V3,
        "python-module-source",
        "backend-import",
        "global nominal-alpha v3 import",
        module="nominal_alpha_dispatch_core_v3",
    )
    add(
        "data:a4972-global-prefix72-source-manifest",
        A4972_MANIFEST,
        "json-alpha-source-metadata",
        "profile-preflight",
        "WPP_PROFILE_V2 B49..B71,W1 source contract",
    )
    add(
        "data:a4972-global-prefix72-source-audit",
        A4972_AUDIT,
        "json-alpha-source-audit",
        "profile-preflight",
        "WPP_PROFILE_V2 a4972 source authorization",
    )
    add(
        "data:a4972-global-prefix72-independent-join-audit",
        A4972_JOIN_AUDIT,
        "json-alpha-source-audit",
        "profile-preflight",
        "WPP_PROFILE_V2 independent v3/a4972 join",
    )

    input_contract = [
        {
            key: entry[key]
            for key in ("id", "root", "path", "kind", "bytes", "sha256")
        }
        for entry in inputs
    ]
    manifest: dict[str, Any] = {
        "schema": "nf-reusable-nominal-mm-translator-profile-v2",
        "status": "FROZEN_STATIC_INPUT_CLOSURE_SOURCE_ONLY",
        "profileId": "WPP_PROFILE_V2",
        "profileVersion": 2,
        "leanStartedByThisProducer": False,
        "producer": {"path": relative(THIS), "sha256": sha256(THIS)},
        "extends": {
            "profileId": "WPP_PROFILE_V1",
            "profileVersion": 1,
            "manifestInputId": "profile:WPP_PROFILE_V1",
            "manifestSha256": V1_SHA256,
            "inputCount": v1["inputCount"],
            "inputSetSha256": v1["inputSetSha256"],
            "inheritedEntriesByteExact": True,
        },
        "workspaceRoot": dict(v1["workspaceRoot"]),
        "scope": {
            **dict(v1["scope"]),
            "theoryProfile": (
                "accepted NF/WPP syntax, structural FV, primitive leaves, and "
                "global nominal-alpha B1..B71,W1 through ordinal 72"
            ),
            "v2Extension": (
                "pinned nominal_alpha_dispatch_core_v3 plus accepted a4972 "
                "source metadata; kernel frontier remains runtime-authorized"
            ),
        },
        "contracts": {
            **dict(v1["contracts"]),
            "alphaGlobalEndOrdinal": 72,
            "alphaGlobalBaseRecordCount": 71,
            "alphaGlobalWppRecordCount": 1,
            "globalAlphaPrefix72": GLOBAL_PREFIX72_CONTRACT,
            "a4972SourceMetadata": {
                "sourceManifestSha256": A4972_MANIFEST_SHA256,
                "sourceAuditSha256": A4972_AUDIT_SHA256,
                "independentJoinAuditSha256": A4972_JOIN_AUDIT_SHA256,
                "successorSourceHashOrderSha256":
                    "F5A3BAD8C928365ACB77E6C442AD7063DE80DDBC0D95B47DC83FA9980302C854",
                "importChainSha256":
                    "157CF0DDB86EBDA8C4EE88973F45616639B890BFAC6C1E8D56521DD268CA192E",
                "w1": {
                    "globalOrdinal": 72,
                    "surface": "wpp",
                    "surfaceOrdinal": 1,
                    "label": "df-iso",
                    "module": "NominalAlphaRepairedWpp001001IsoStructural001",
                    "sourceSha256":
                        "CF76E477A68EE513FDEDFC3F7AC502A0B321BBD8EEFC9666CBE9FF1E3618CB61",
                },
            },
        },
        "runtimeAuthorizedInputs": list(v1["runtimeAuthorizedInputs"]),
        "orderedInputSets": dict(v1["orderedInputSets"]),
        "inputCount": len(inputs),
        "pythonModuleCount": sum(
            entry["kind"] == "python-module-source" for entry in inputs
        ),
        "fixedDataCount": sum(
            entry["kind"] != "python-module-source" for entry in inputs
        ),
        "inputSetSha256": canonical_sha256(input_contract),
        "inputs": inputs,
    }
    require(
        manifest["inputCount"] == 97
        and manifest["pythonModuleCount"] == 20
        and manifest["fixedDataCount"] == 77,
        "WPP_PROFILE_V2 bounded census changed",
    )
    content = (json.dumps(manifest, indent=2) + "\n").encode("utf-8")
    if OUT.exists():
        require(OUT.read_bytes() == content, f"append-only profile differs: {OUT}")
    else:
        OUT.write_bytes(content)
    print(
        json.dumps(
            {
                "status": "PASS_WPP_PROFILE_V2_MANIFEST_BUILT",
                "path": str(OUT),
                "sha256": sha256(OUT),
                "bytes": OUT.stat().st_size,
                "inputCount": manifest["inputCount"],
                "pythonModuleCount": manifest["pythonModuleCount"],
                "fixedDataCount": manifest["fixedDataCount"],
                "globalAlphaEndOrdinal": 72,
                "leanStarted": False,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
