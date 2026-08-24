#!/usr/bin/env python3
"""Append-only nominal-alpha frontier loader with reflected-module overrides.

Version 1 derives every import from the original source manifest and only
collects output roots from ``compiles`` records.  Reflected successors need a
small, fail-closed extension: an accepted resource may replace a module name at
an ordinal and may publish accepted oleans through ``acceptedModules`` or
``moduleOverrides``.  The call construction remains byte-for-byte delegated to
the pinned v1 core.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
CORE_V1 = HERE / "nominal_alpha_dispatch_core_v1.py"
CORE_V1_SHA256 = "9CE336D6AE0FD2545759F232455456B6ED2C8118097E1AB38CEEBF9C626A5D8C"
WORKSPACE = HERE.parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


if sha256(CORE_V1) != CORE_V1_SHA256:
    raise RuntimeError("pinned nominal-alpha dispatch core v1 identity changed")
_spec = importlib.util.spec_from_file_location(
    "nominal_alpha_dispatch_core_v1_pinned", CORE_V1
)
if _spec is None or _spec.loader is None:
    raise RuntimeError("cannot load pinned nominal-alpha dispatch core v1")
base = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(base)

CALL_MAP = base.CALL_MAP
MANIFEST = base.MANIFEST
MANIFEST_SHA256 = base.MANIFEST_SHA256


def _workspace_path(value: str | Path) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = WORKSPACE / path
    return path.resolve()


def _accepted_status(data: dict[str, Any], end_ordinal: int) -> bool:
    return (
        str(data.get("status", "")).startswith("PASS_KERNEL_FIRST_USE_PREFIX_")
        and data.get("firstUsePrefix", {}).get("endOrdinal") == end_ordinal
    )


class AlphaFrontier(base.AlphaFrontier):
    """Accepted alpha frontier with exact reflected-module import support."""

    @classmethod
    def load(
        cls,
        resource: Path,
        expected_sha256: str,
        end_ordinal: int,
    ) -> "AlphaFrontier":
        resource = resource.resolve()
        actual = sha256(resource)
        if actual != expected_sha256.upper():
            raise RuntimeError(f"nominal alpha frontier resource changed: {actual}")
        data = json.loads(resource.read_text(encoding="utf-8"))
        if not _accepted_status(data, end_ordinal):
            raise RuntimeError("nominal alpha frontier resource is not accepted")
        if not 1 <= end_ordinal <= len(base._base_records):
            raise RuntimeError("nominal alpha frontier ordinal out of range")

        records = base._base_records[:end_ordinal]
        labels = tuple(str(record["label"]) for record in records)
        overrides: dict[int, str] = {}

        def collect_overrides(rows: Any) -> None:
            for row in rows or []:
                if "ordinal" not in row or not row.get("module"):
                    continue
                ordinal = int(row["ordinal"])
                module = str(row["module"])
                if not 1 <= ordinal <= end_ordinal:
                    raise RuntimeError(
                        f"module override outside accepted frontier: {ordinal}"
                    )
                prior = overrides.get(ordinal)
                if prior is not None and prior != module:
                    raise RuntimeError(
                        f"conflicting module overrides at ordinal {ordinal}"
                    )
                overrides[ordinal] = module

        collect_overrides(data.get("compiles"))
        collect_overrides(data.get("acceptedModules"))
        collect_overrides(data.get("moduleOverrides"))
        imports = tuple(
            "NominalDfEu"
            if ordinal == 1
            else "NominalAlphaRepairedDfNfc001"
            if ordinal == 2
            else overrides.get(ordinal, str(record["module"]))
            for ordinal, record in enumerate(records, start=1)
        )

        extra_olean_roots: list[Path] = []
        seen_resources: set[Path] = set()

        def collect_output(row: dict[str, Any]) -> None:
            if row.get("exitCode") not in (None, 0):
                return
            output_name = row.get("outputPath") or row.get("oleanPath")
            if not output_name:
                return
            output = _workspace_path(str(output_name))
            if not output.is_file():
                raise RuntimeError(f"accepted nominal-alpha olean is missing: {output}")
            expected = row.get("outputSha256") or row.get("oleanSha256")
            if expected and sha256(output) != str(expected).upper():
                raise RuntimeError(f"accepted nominal-alpha olean changed: {output}")
            root = output.parent
            if root not in extra_olean_roots:
                extra_olean_roots.append(root)

        def collect_roots(resource_path: Path, resource_data: dict[str, Any]) -> None:
            resolved_resource = resource_path.resolve()
            if resolved_resource in seen_resources:
                raise RuntimeError("nominal alpha frontier parent cycle")
            seen_resources.add(resolved_resource)
            for key in ("compiles", "acceptedModules", "moduleOverrides"):
                for row in resource_data.get(key, []) or []:
                    collect_output(row)
            audit = resource_data.get("audit")
            if isinstance(audit, dict):
                collect_output(audit)

            parent = resource_data.get("parent", {})
            parent_name = parent.get("resource") or parent.get("resourcePath")
            parent_sha = parent.get("resourceSha256")
            if not parent_name or not parent_sha:
                return
            parent_path = _workspace_path(str(parent_name))
            if sha256(parent_path) != str(parent_sha).upper():
                raise RuntimeError("nominal alpha frontier parent identity changed")
            parent_data = json.loads(parent_path.read_text(encoding="utf-8"))
            collect_roots(parent_path, parent_data)

        collect_roots(resource, data)
        return cls(
            end_ordinal,
            resource,
            actual,
            labels,
            imports,
            tuple(extra_olean_roots),
        )

