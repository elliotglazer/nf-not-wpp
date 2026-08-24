#!/usr/bin/env python3
"""Fail-closed global-record nominal-alpha frontier loader.

The v1/v2 dispatcher uses the 71 ``base`` records as its ordinal space.  The
source manifest is larger: its exact file order is B1..B71 followed by
W1..W26.  This append-only successor gives that 97-record order an explicit
global ordinal without changing any legacy load through B71.

For a frontier which crosses the old B71 boundary, the accepted kernel
resource must carry :func:`global_record_contract` verbatim and must descend
from the pinned, accepted B1..B48 frontier.  This prevents a surface ordinal
such as W1 from being confused with either B1 or global ordinal 1.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import re
from pathlib import Path
from typing import Any, Mapping, Sequence


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
CORE_V2 = HERE / "nominal_alpha_dispatch_core_v2.py"
CORE_V2_SHA256 = "78AB2C0DACCB170D121D811B082C8256DE3531369E687ACDE6C46C6675F82FB3"
MANIFEST = HERE / "generated_nominal_alpha_batch_003/NominalAlphaRepairedAll003.json"
MANIFEST_SHA256 = "733E17BAA3798E165989FE991BF26A0AA69E45A1FAECB9EC7CA711B9FC732E47"
ACCEPTED_BASE_PREFIX48_RESOURCE = HERE / "a3848k1/resource.json"
ACCEPTED_BASE_PREFIX48_RESOURCE_SHA256 = (
    "5299F0DA88C07150FCEBB96F2C04CC0DCDFF6C3FC48265C65BA407BC8DBC9FCA"
)

BASE_RECORD_COUNT = 71
WPP_RECORD_COUNT = 26
GLOBAL_RECORD_COUNT = 97
LEGACY_ACCEPTED_END_ORDINAL = 48
GLOBAL_CONTRACT_SCHEMA = "nf-wpp-nominal-alpha-global-record-prefix-v3"

# These are portable canonical fingerprints, not hashes of absolute source
# paths.  They bind the ordered theorem/call contract and all source/semantic
# hashes recorded in the already-pinned manifest.
BASE_PREFIX48_RECORD_ORDER_SHA256 = (
    "8A88DF5DB2DCFD214FFB4835D481C601D66A2030F950E687D8DE42F8B75E95CD"
)
BASE_PREFIX48_SOURCE_HASH_ORDER_SHA256 = (
    "5381495822D152AD1FC8127617563BFD0AD19FCB6CF95140DDEB990D3A9220F5"
)
BASE_PREFIX71_RECORD_ORDER_SHA256 = (
    "4A0AC2F1CE256F4B16B0015F95A1C180E37DBFBC46BB79391AC8749824CF048A"
)
GLOBAL_PREFIX72_RECORD_ORDER_SHA256 = (
    "0E5231014445B25C31737A520C4F4516101E27E9BAAEF5543B264DC7388FD0D5"
)
GLOBAL_PREFIX72_SOURCE_HASH_ORDER_SHA256 = (
    "FCDCD473111EAD48A6089E2049C0F273C106733CB90DBE87722C586F65726FFA"
)
GLOBAL_ALL97_RECORD_ORDER_SHA256 = (
    "473F280297221659F21992BA67D49A4DD2A90B4413AD586AA9DA69EA31A9E035"
)

_HEX64 = re.compile(r"[0-9A-F]{64}")
_MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")
_RECORD_FIELDS = (
    ("label", "label"),
    ("category", "category"),
    ("theorem", "theorem"),
    ("floating", "floating"),
    ("dv", "dv"),
    ("essential", "essential"),
    ("surface", "surface"),
    ("surfaceOrdinal", "surface_ordinal"),
    ("module", "module"),
    ("import", "import"),
    ("sourceSha256", "source_sha256"),
    ("sourceBytes", "source_bytes"),
    ("semanticBlockSha256", "semantic_block_sha256"),
    ("nominalBlockSha256", "nominal_block_sha256"),
    ("rawSchemaSha256", "raw_schema_sha256"),
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def _canonical_sha256(value: Any) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest().upper()


def _checked_global_ordinal(value: Any) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise RuntimeError("nominal alpha global ordinal must be an integer")
    if not 1 <= value <= GLOBAL_RECORD_COUNT:
        raise RuntimeError("nominal alpha global ordinal out of range")
    return value


def _workspace_path(value: str | Path) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = WORKSPACE / path
    return path.resolve()


for _path, _expected, _message in (
    (CORE_V2, CORE_V2_SHA256, "nominal-alpha dispatch core v2 identity changed"),
    (MANIFEST, MANIFEST_SHA256, "nominal-alpha 97-record manifest changed"),
):
    if sha256(_path) != _expected:
        raise RuntimeError(_message)

_spec = importlib.util.spec_from_file_location(
    "nominal_alpha_dispatch_core_v2_pinned_by_v3", CORE_V2
)
if _spec is None or _spec.loader is None:
    raise RuntimeError("cannot load pinned nominal-alpha dispatch core v2")
legacy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(legacy)

CALL_MAP = legacy.CALL_MAP
_manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))


def _record_contract(record: Mapping[str, Any], global_ordinal: int) -> dict[str, Any]:
    return {
        "globalOrdinal": global_ordinal,
        **{output: record.get(source) for output, source in _RECORD_FIELDS},
    }


def _validate_global_records(
    records: Sequence[Mapping[str, Any]], call_map: Mapping[str, Mapping[str, Any]]
) -> tuple[dict[str, Any], ...]:
    """Validate and copy the exact B1..B71,W1..W26 global record order."""

    copied = tuple(dict(record) for record in records)
    if len(copied) != GLOBAL_RECORD_COUNT:
        raise RuntimeError("nominal-alpha global record census changed")
    expected_surfaces = (
        [("base", ordinal) for ordinal in range(1, BASE_RECORD_COUNT + 1)]
        + [("wpp", ordinal) for ordinal in range(1, WPP_RECORD_COUNT + 1)]
    )
    actual_surfaces = []
    for record in copied:
        surface_ordinal = record.get("surface_ordinal")
        if not isinstance(surface_ordinal, int) or isinstance(surface_ordinal, bool):
            raise RuntimeError("nominal-alpha surface ordinal is not an integer")
        actual_surfaces.append((str(record.get("surface")), surface_ordinal))
    if actual_surfaces != expected_surfaces:
        raise RuntimeError("nominal-alpha global surface order changed")

    labels = [str(record.get("label", "")) for record in copied]
    if len(set(labels)) != len(labels) or set(labels) != set(call_map):
        raise RuntimeError("nominal-alpha global label/call-map census changed")

    for global_ordinal, record in enumerate(copied, start=1):
        label = str(record.get("label", ""))
        module = str(record.get("module", ""))
        if not _MODULE.fullmatch(module):
            raise RuntimeError(
                f"invalid global alpha module at ordinal {global_ordinal}: {module}"
            )
        if record.get("import") != module:
            raise RuntimeError(
                f"global alpha import/module mismatch at ordinal {global_ordinal}"
            )
        entry = call_map[label]
        for key in ("module", "theorem", "floating", "dv", "essential"):
            if record.get(key) != entry.get(key):
                raise RuntimeError(
                    f"global alpha call-map mismatch at ordinal {global_ordinal}: {key}"
                )
        source_name = Path(str(record.get("source", ""))).name
        if source_name != f"{module}.lean":
            raise RuntimeError(
                f"global alpha source/module mismatch at ordinal {global_ordinal}"
            )
        for key in (
            "source_sha256",
            "semantic_block_sha256",
            "nominal_block_sha256",
        ):
            value = str(record.get(key, ""))
            if not _HEX64.fullmatch(value):
                raise RuntimeError(
                    f"invalid global alpha {key} at ordinal {global_ordinal}"
                )
        raw_schema = record.get("raw_schema_sha256")
        if raw_schema is not None and not _HEX64.fullmatch(str(raw_schema)):
            raise RuntimeError(
                f"invalid global alpha raw schema hash at ordinal {global_ordinal}"
            )
    return copied


GLOBAL_RECORDS = _validate_global_records(_manifest["records"], CALL_MAP)

# This is the central backwards-compatibility invariant: the legacy v2 base
# order must be literally the first 71 records of the new global order.
if list(GLOBAL_RECORDS[:BASE_RECORD_COUNT]) != list(legacy.base._base_records):
    raise RuntimeError("global alpha B1..B71 records differ from pinned v2")


def record_fingerprint(global_ordinal: int) -> str:
    global_ordinal = _checked_global_ordinal(global_ordinal)
    return _canonical_sha256(
        _record_contract(GLOBAL_RECORDS[global_ordinal - 1], global_ordinal)
    )


def prefix_record_order_sha256(end_ordinal: int) -> str:
    end_ordinal = _checked_global_ordinal(end_ordinal)
    return _canonical_sha256(
        [
            _record_contract(record, global_ordinal)
            for global_ordinal, record in enumerate(
                GLOBAL_RECORDS[:end_ordinal], start=1
            )
        ]
    )


def prefix_source_hash_order_sha256(end_ordinal: int) -> str:
    end_ordinal = _checked_global_ordinal(end_ordinal)
    return _canonical_sha256(
        [
            str(record["source_sha256"])
            for record in GLOBAL_RECORDS[:end_ordinal]
        ]
    )


for _actual, _expected, _message in (
    (
        prefix_record_order_sha256(48),
        BASE_PREFIX48_RECORD_ORDER_SHA256,
        "accepted B1..B48 record order/hash contract changed",
    ),
    (
        prefix_source_hash_order_sha256(48),
        BASE_PREFIX48_SOURCE_HASH_ORDER_SHA256,
        "accepted B1..B48 source-hash order changed",
    ),
    (
        prefix_record_order_sha256(71),
        BASE_PREFIX71_RECORD_ORDER_SHA256,
        "B1..B71 record order/hash contract changed",
    ),
    (
        prefix_record_order_sha256(72),
        GLOBAL_PREFIX72_RECORD_ORDER_SHA256,
        "B1..B71,W1 record order/hash contract changed",
    ),
    (
        prefix_source_hash_order_sha256(72),
        GLOBAL_PREFIX72_SOURCE_HASH_ORDER_SHA256,
        "B1..B71,W1 source-hash order changed",
    ),
    (
        prefix_record_order_sha256(97),
        GLOBAL_ALL97_RECORD_ORDER_SHA256,
        "97-record global alpha order/hash contract changed",
    ),
):
    if _actual != _expected:
        raise RuntimeError(_message)


def global_record_contract(end_ordinal: int) -> dict[str, Any]:
    """Return the exact resource-side provenance contract for a global prefix."""

    end_ordinal = _checked_global_ordinal(end_ordinal)
    last = GLOBAL_RECORDS[end_ordinal - 1]
    return {
        "schema": GLOBAL_CONTRACT_SCHEMA,
        "manifestSha256": MANIFEST_SHA256,
        "globalEndOrdinal": end_ordinal,
        "globalRecordCount": end_ordinal,
        "baseRecordCount": min(end_ordinal, BASE_RECORD_COUNT),
        "wppRecordCount": max(0, end_ordinal - BASE_RECORD_COUNT),
        "recordOrderSha256": prefix_record_order_sha256(end_ordinal),
        "sourceHashOrderSha256": prefix_source_hash_order_sha256(end_ordinal),
        "acceptedBasePrefix48RecordOrderSha256": (
            BASE_PREFIX48_RECORD_ORDER_SHA256
        ),
        "acceptedBasePrefix48SourceHashOrderSha256": (
            BASE_PREFIX48_SOURCE_HASH_ORDER_SHA256
        ),
        "acceptedBasePrefix48ResourceSha256": (
            ACCEPTED_BASE_PREFIX48_RESOURCE_SHA256
        ),
        "firstRecord": {
            "globalOrdinal": 1,
            "surface": "base",
            "surfaceOrdinal": 1,
            "label": str(GLOBAL_RECORDS[0]["label"]),
        },
        "lastRecord": {
            "globalOrdinal": end_ordinal,
            "surface": str(last["surface"]),
            "surfaceOrdinal": int(last["surface_ordinal"]),
            "label": str(last["label"]),
        },
    }


def _validate_global_resource(data: Mapping[str, Any], end_ordinal: int) -> None:
    status_prefix = f"PASS_KERNEL_FIRST_USE_PREFIX_{end_ordinal}"
    status = str(data.get("status", ""))
    first_use = data.get("firstUsePrefix")
    if not isinstance(first_use, Mapping):
        raise RuntimeError("global nominal alpha first-use prefix is missing")
    if not (
        (status == status_prefix or status.startswith(status_prefix + "_"))
        and isinstance(data.get("trust"), int)
        and not isinstance(data.get("trust"), bool)
        and data.get("trust") == 0
        and type(first_use.get("startOrdinal")) is int
        and first_use.get("startOrdinal") == 1
        and type(first_use.get("endOrdinal")) is int
        and first_use.get("endOrdinal") == end_ordinal
        and type(first_use.get("coveredCount")) is int
        and first_use.get("coveredCount") == end_ordinal
        and type(first_use.get("nextOrdinal")) is int
        and first_use.get("nextOrdinal") == end_ordinal + 1
    ):
        raise RuntimeError("global nominal alpha frontier resource is not accepted")
    if data.get("globalRecordContract") != global_record_contract(end_ordinal):
        raise RuntimeError("global nominal alpha record provenance contract changed")
    audit = data.get("audit")
    if not isinstance(audit, Mapping) or not (
        audit.get("exitCode") == 0
        and audit.get("killed") is False
        and audit.get("emptyStderr") is True
        and audit.get("exactAllowedThreeAll") is True
        and audit.get("forbiddenAxiomMatches") == []
    ):
        raise RuntimeError("global nominal alpha exact-three audit is not accepted")


class AlphaFrontier(legacy.AlphaFrontier):
    """Accepted global alpha frontier, compatible with v2 through B71."""

    def __init__(
        self,
        end_ordinal: int,
        resource: Path,
        resource_sha256: str,
        labels: tuple[str, ...],
        imports: tuple[str, ...],
        extra_olean_roots: tuple[Path, ...],
    ) -> None:
        super().__init__(
            end_ordinal,
            resource,
            resource_sha256,
            labels,
            imports,
            extra_olean_roots,
        )
        self.global_record_contract = global_record_contract(end_ordinal)
        self.record_fingerprints = tuple(
            record_fingerprint(ordinal) for ordinal in range(1, end_ordinal + 1)
        )
        self.global_resource_contract_verified = False

    @classmethod
    def load(
        cls,
        resource: Path,
        expected_sha256: str,
        end_ordinal: int,
    ) -> "AlphaFrontier":
        end_ordinal = _checked_global_ordinal(end_ordinal)
        # Delegating the entire legacy range is deliberate.  It makes v3 an
        # observationally exact successor for every already-accepted B-prefix.
        if end_ordinal <= BASE_RECORD_COUNT:
            return super().load(resource, expected_sha256, end_ordinal)
        resource = resource.resolve()
        actual = sha256(resource)
        if actual != expected_sha256.upper():
            raise RuntimeError(f"nominal alpha frontier resource changed: {actual}")
        data = json.loads(resource.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise RuntimeError("global nominal alpha resource must be an object")
        _validate_global_resource(data, end_ordinal)

        records = GLOBAL_RECORDS[:end_ordinal]
        labels = tuple(str(record["label"]) for record in records)
        overrides: dict[int, str] = {}
        extra_olean_roots: list[Path] = []
        seen_resources: set[Path] = set()
        seen_resource_hashes: set[str] = set()
        extension_outputs: dict[int, tuple[str, Path, str]] = {}

        def collect_output(row: Mapping[str, Any]) -> Path | None:
            if row.get("exitCode") not in (None, 0):
                return None
            output_name = row.get("outputPath") or row.get("oleanPath")
            if not output_name:
                return None
            output = _workspace_path(str(output_name))
            if not output.is_file():
                raise RuntimeError(f"accepted nominal-alpha olean is missing: {output}")
            expected = row.get("outputSha256") or row.get("oleanSha256")
            if expected is None or not _HEX64.fullmatch(str(expected).upper()):
                raise RuntimeError(f"accepted nominal-alpha olean hash is missing: {output}")
            if sha256(output) != str(expected).upper():
                raise RuntimeError(f"accepted nominal-alpha olean changed: {output}")
            root = output.parent
            if root not in extra_olean_roots:
                extra_olean_roots.append(root)
            return output

        def collect_row(row: Mapping[str, Any], key: str) -> None:
            ordinal_value = row.get("ordinal")
            if ordinal_value is None:
                collect_output(row)
                return
            if not isinstance(ordinal_value, int) or isinstance(ordinal_value, bool):
                raise RuntimeError("global alpha resource ordinal is not an integer")
            ordinal = ordinal_value
            if not 1 <= ordinal <= end_ordinal:
                raise RuntimeError(
                    f"module override outside accepted global frontier: {ordinal}"
                )
            module_value = row.get("module")
            if module_value:
                module = str(module_value)
                if not _MODULE.fullmatch(module):
                    raise RuntimeError(f"invalid module override at ordinal {ordinal}")
                prior = overrides.get(ordinal)
                if prior is not None and prior != module:
                    raise RuntimeError(
                        f"conflicting module overrides at ordinal {ordinal}"
                    )
                overrides[ordinal] = module
            else:
                module = ""
            output = collect_output(row)

            if ordinal <= LEGACY_ACCEPTED_END_ORDINAL or key == "moduleOverrides":
                return
            record = records[ordinal - 1]
            if row.get("label") != record["label"]:
                raise RuntimeError(f"global alpha label mismatch at ordinal {ordinal}")
            if row.get("theorem") != record["theorem"]:
                raise RuntimeError(f"global alpha theorem mismatch at ordinal {ordinal}")
            expected_hash = row.get("outputSha256") or row.get("oleanSha256")
            if output is None or not module or expected_hash is None:
                raise RuntimeError(
                    f"global alpha output provenance missing at ordinal {ordinal}"
                )
            contract = (module, output, str(expected_hash).upper())
            prior_output = extension_outputs.get(ordinal)
            if prior_output is not None and prior_output != contract:
                raise RuntimeError(
                    f"conflicting global alpha outputs at ordinal {ordinal}"
                )
            extension_outputs[ordinal] = contract

        def collect_resource(resource_path: Path, resource_data: Mapping[str, Any]) -> None:
            resolved = resource_path.resolve()
            if resolved in seen_resources:
                raise RuntimeError("nominal alpha frontier parent cycle")
            seen_resources.add(resolved)
            resource_hash = sha256(resolved)
            seen_resource_hashes.add(resource_hash)

            for key in ("compiles", "acceptedModules", "moduleOverrides"):
                rows = resource_data.get(key, []) or []
                if not isinstance(rows, list):
                    raise RuntimeError(f"global nominal alpha {key} must be a list")
                for row in rows:
                    if not isinstance(row, Mapping):
                        raise RuntimeError(f"global nominal alpha {key} row is invalid")
                    collect_row(row, key)
            audit_row = resource_data.get("audit")
            if isinstance(audit_row, Mapping):
                collect_output(audit_row)

            parent = resource_data.get("parent")
            if not isinstance(parent, Mapping):
                return
            parent_name = parent.get("resource") or parent.get("resourcePath")
            parent_sha = parent.get("resourceSha256")
            if not parent_name and not parent_sha:
                return
            if not parent_name or not parent_sha:
                raise RuntimeError("nominal alpha frontier parent provenance is incomplete")
            parent_path = _workspace_path(str(parent_name))
            parent_actual = sha256(parent_path)
            if parent_actual != str(parent_sha).upper():
                raise RuntimeError("nominal alpha frontier parent identity changed")
            parent_data = json.loads(parent_path.read_text(encoding="utf-8"))
            if not isinstance(parent_data, Mapping):
                raise RuntimeError("nominal alpha frontier parent must be an object")
            collect_resource(parent_path, parent_data)

        collect_resource(resource, data)
        if ACCEPTED_BASE_PREFIX48_RESOURCE_SHA256 not in seen_resource_hashes:
            raise RuntimeError("global alpha frontier does not descend from accepted B1..B48")

        imports = tuple(
            "NominalDfEu"
            if ordinal == 1
            else "NominalAlphaRepairedDfNfc001"
            if ordinal == 2
            else overrides.get(ordinal, str(record["module"]))
            for ordinal, record in enumerate(records, start=1)
        )
        expected_extension = set(
            range(LEGACY_ACCEPTED_END_ORDINAL + 1, end_ordinal + 1)
        )
        if set(extension_outputs) != expected_extension:
            missing = sorted(expected_extension - set(extension_outputs))
            extra = sorted(set(extension_outputs) - expected_extension)
            raise RuntimeError(
                f"global alpha output coverage changed: missing={missing} extra={extra}"
            )
        for ordinal in sorted(expected_extension):
            module, output, output_hash = extension_outputs[ordinal]
            if module != imports[ordinal - 1]:
                raise RuntimeError(
                    f"global alpha output/import mismatch at ordinal {ordinal}"
                )
            if sha256(output) != output_hash:
                raise RuntimeError(
                    f"global alpha output hash changed at ordinal {ordinal}"
                )

        frontier = cls(
            end_ordinal,
            resource,
            actual,
            labels,
            imports,
            tuple(extra_olean_roots),
        )
        for ordinal in sorted(expected_extension):
            module, _output, output_hash = extension_outputs[ordinal]
            candidates = [
                root / f"{module}.olean"
                for root in frontier.olean_roots
                if (root / f"{module}.olean").is_file()
            ]
            if not candidates or sha256(candidates[0]) != output_hash:
                raise RuntimeError(
                    f"LEAN_PATH would not resolve accepted global alpha ordinal {ordinal}"
                )
        frontier.global_resource_contract_verified = True
        return frontier


__all__ = [
    "ACCEPTED_BASE_PREFIX48_RESOURCE",
    "ACCEPTED_BASE_PREFIX48_RESOURCE_SHA256",
    "AlphaFrontier",
    "BASE_PREFIX48_RECORD_ORDER_SHA256",
    "BASE_PREFIX48_SOURCE_HASH_ORDER_SHA256",
    "CALL_MAP",
    "GLOBAL_ALL97_RECORD_ORDER_SHA256",
    "GLOBAL_PREFIX72_RECORD_ORDER_SHA256",
    "GLOBAL_PREFIX72_SOURCE_HASH_ORDER_SHA256",
    "GLOBAL_RECORDS",
    "MANIFEST",
    "MANIFEST_SHA256",
    "global_record_contract",
    "prefix_record_order_sha256",
    "prefix_source_hash_order_sha256",
    "record_fingerprint",
    "sha256",
]
