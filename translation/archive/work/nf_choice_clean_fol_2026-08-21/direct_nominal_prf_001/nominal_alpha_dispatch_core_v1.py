#!/usr/bin/env python3
"""Generic fail-closed integration core for accepted nominal alpha frontiers."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Mapping


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "generated_nominal_alpha_batch_003/NominalAlphaRepairedAll003.json"
MANIFEST_SHA256 = "733E17BAA3798E165989FE991BF26A0AA69E45A1FAECB9EC7CA711B9FC732E47"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


if sha256(MANIFEST) != MANIFEST_SHA256:
    raise RuntimeError("exact nominal alpha call-map manifest identity changed")
_manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
_base_records = sorted(
    (record for record in _manifest["records"] if record["surface"] == "base"),
    key=lambda record: int(record["surface_ordinal"]),
)
if [int(record["surface_ordinal"]) for record in _base_records] != list(range(1, 72)):
    raise RuntimeError("exact nominal base-alpha ordinal census changed")
CALL_MAP: dict[str, dict[str, Any]] = _manifest["call_map"]


class AlphaFrontier:
    def __init__(
        self,
        end_ordinal: int,
        resource: Path,
        resource_sha256: str,
        labels: tuple[str, ...],
        imports: tuple[str, ...],
        extra_olean_roots: tuple[Path, ...],
    ) -> None:
        self.end_ordinal = end_ordinal
        self.resource = resource
        self.resource_sha256 = resource_sha256
        self.labels = labels
        self.imports = imports
        self.extra_olean_roots = extra_olean_roots

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
        if (
            not str(data.get("status", "")).startswith("PASS_KERNEL_FIRST_USE_PREFIX_")
            or data.get("firstUsePrefix", {}).get("endOrdinal") != end_ordinal
        ):
            raise RuntimeError("nominal alpha frontier resource is not accepted")
        if not 1 <= end_ordinal <= len(_base_records):
            raise RuntimeError("nominal alpha frontier ordinal out of range")
        records = _base_records[:end_ordinal]
        labels = tuple(str(record["label"]) for record in records)
        imports = tuple(
            "NominalDfEu" if ordinal == 1
            else "NominalAlphaRepairedDfNfc001" if ordinal == 2
            else str(record["module"])
            for ordinal, record in enumerate(records, start=1)
        )
        extra_olean_roots: list[Path] = []
        seen_resources: set[Path] = set()

        def collect_roots(resource_path: Path, resource_data: dict[str, Any]) -> None:
            resolved_resource = resource_path.resolve()
            if resolved_resource in seen_resources:
                raise RuntimeError("nominal alpha frontier parent cycle")
            seen_resources.add(resolved_resource)
            for compile_record in resource_data.get("compiles", []):
                if compile_record.get("exitCode") != 0:
                    continue
                output = compile_record.get("outputPath")
                if not output:
                    continue
                root = Path(output).resolve().parent
                if root not in extra_olean_roots:
                    extra_olean_roots.append(root)
            parent = resource_data.get("parent", {})
            parent_name = parent.get("resource") or parent.get("resourcePath")
            parent_sha = parent.get("resourceSha256")
            if not parent_name or not parent_sha:
                return
            parent_path = Path(parent_name)
            if not parent_path.is_absolute():
                parent_path = HERE.parents[2] / parent_path
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

    @property
    def olean_roots(self) -> tuple[Path, ...]:
        return (
            HERE / "df_eu_compile_attempt_002",
            HERE / "nominal_alpha_repaired_dfnfc_compile_attempt_004",
            HERE / "nominal_alpha_batch_kernel_001",
            *self.extra_olean_roots,
        )

    def definition_leaf_call(
        self,
        emitter: Any,
        label: str,
        subst: Mapping[str, Any],
        essentials: list[str],
    ) -> str | None:
        if label not in self.labels:
            return None
        if essentials:
            raise RuntimeError(
                f"accepted alpha definition unexpectedly has essentials: {label}"
            )
        if label == "df-eu":
            args = {name: emitter.expr(subst[name]) for name in ("x", "y", "ph")}
            return (
                f"Nominal.dfEu {args['x']} {args['y']} {args['ph']} "
                f"{emitter.dv_tactic(subst['x'], subst['y'])} "
                f"{emitter.dv_tactic(subst['y'], subst['ph'])}"
            )
        entry = CALL_MAP[label]
        if entry.get("essential") != []:
            raise RuntimeError(f"alpha call-map essential contract changed: {label}")
        pieces = [entry["theorem"]]
        pieces.extend(emitter.expr(subst[name]) for name in entry["floating"])
        pieces.extend(
            emitter.dv_tactic(subst[left], subst[right])
            for left, right in entry["dv"]
        )
        return " ".join(pieces)
