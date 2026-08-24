#!/usr/bin/env python3
"""Independent reversible source audit of reusable compact chunk 11.

No Lean process is started.  This pins the accepted old chunk-11 source,
trace, full-source audit, and reversible 60KB split together with the fresh
reusable-translator compact successor.  It reconstructs both split chains and
checks exact preservation of theorem labels/statements, proof operations,
application/substitution/dependency traces, DV-cache targets, and proof-DAG
suffixes.  Every new nonmembership cache must use the deterministic compact
FV certificate and no generic cache fallback is permitted.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import time


HERE = Path(__file__).resolve().parent
THIS = Path(__file__).resolve()
TRANSLATOR = HERE / "reusable_nominal_mm_translator_v1.py"
MIXIN = HERE / "compact_fv_normalize_mixin_v1.py"
NEW = HERE / "reusable_nominal_mm_translator_v1_chunk011_compact_001"
NEW_RESOURCE = NEW / "resource.json"
NEW_SOURCE_AUDIT = NEW / "source_audit.json"
OLD = HERE / "generated_nominal_wpp_replay_prefix48_cached_structural_fv_chunk011_001"
OLD_SOURCE = OLD / "NominalWPPReplayChunk011.lean"
OLD_MANIFEST = OLD / "nominal_wpp_replay_chunk_011_manifest.json"
OLD_SOURCE_AUDIT = (
    HERE / "nominal_wpp_prefix48_cached_structural_fv_chunk011_source_audit_001"
    / "resource.json"
)
OLD_SPLIT = (
    HERE
    / "generated_nominal_wpp_replay_prefix48_cached_structural_fv_chunk011_split60k_001"
    / "resource.json"
)
OLD_SPLIT_AUDIT = (
    HERE
    / "nominal_wpp_prefix48_cached_structural_fv_chunk011_split60k_source_audit_001"
    / "resource.json"
)
PREDECESSOR = (
    HERE / "reusable_nominal_mm_translator_v1_chunk010_compact_001" / "resource.json"
)
ALPHA48 = HERE / "a3848k1" / "resource.json"
OUTPUT = HERE / "reusable_nominal_mm_translator_v1_chunk011_compact_source_audit_001"
OUTPUT_RESOURCE = OUTPUT / "resource.json"

PINNED = {
    TRANSLATOR: "12A59CDC12DE5F10DCD20D3479F7DD4DB57623B4E3FCBFCA70FE82A515E57F85",
    MIXIN: "CA7493053B75FC9B2EDC0F6C16AE31DE07C5F1A52119F15314BD09D3A165BDA4",
    NEW_RESOURCE: "EE6BA50F8C207822F5012D4B31E2A18C7533732F85FE8D674D43C39BCBF4E5B1",
    NEW_SOURCE_AUDIT: "2E543166369DEC4FC1BAEB7CB2D71409D36A3CBC824B645368E754A83682FC2E",
    OLD_SOURCE: "DF3C2C9A60639728F11A5C70AB36900A27EBD4408F8FC9AB65C54715D5ED52CB",
    OLD_MANIFEST: "54CFC17F8946D78AEB96ADBFD5FACC78272391FC2DCC9A84D1EDE1059FA205F5",
    OLD_SOURCE_AUDIT: "1FF63F9586AEC696AA1A0F483694508B3D5BD89CF1EA78D78D1EB3C70B82DF78",
    OLD_SPLIT: "EBB274B9441BE059A29503ED5CF2AA2F193E042FCB9B2C1768B9B99C0D3D2019",
    OLD_SPLIT_AUDIT: "E404CC95D7ED10088483BCD52928DC7563C76585DFF8AD3540B372F213330697",
    PREDECESSOR: "3F2C7D736EBF7D92BE136362E81AEDDE0259433BE4DEE0631DE3B2E29330DB7A",
    ALPHA48: "5299F0DA88C07150FCEBB96F2C04CC0DCDFF6C3FC48265C65BA407BC8DBC9FCA",
}

START_ORDINAL = 2505
END_ORDINAL = 2754
THEOREM_COUNT = 250
PROOF_OP_COUNT = 16129
APPLICATION_COUNT = 2120
CACHE_COUNT = 748
NONMEMBERSHIP_COUNT = 645
INEQUALITY_COUNT = 103
NEW_PART_COUNT = 16
OLD_PART_COUNT = 15
NEW_AGGREGATE_BYTES = 835095
NEW_AGGREGATE_SHA256 = "B23DABDDD6B5D327108D4FC4751A17AA646BD930766664EFB04C0624426E7F28"
OLD_AGGREGATE_BYTES = 822473
OLD_AGGREGATE_SHA256 = "CE4A5AE16EF420375CBDDCF74BBFB93BC9202D651AA3ED71A5EC2CCD2309A02A"
TRACE_SHA256 = "B7A4785D215F31C4A94B9E23F4BCF8C9E677A4A4EC8CF87DEA69C7BE5279C305"
NEW_UMBRELLA_SHA256 = "86F64DF2029F68B56A978CFC6F4C9F338BEA315055EE86C668B253B6E6D45E56"

START_RE = re.compile(r"(?m)^noncomputable def g_([A-Za-z0-9_]+)\b")
CACHE_RE = re.compile(r"(?m)^  have (dv_cache_[0-9]+) : (.+) := by$")
FORBIDDEN_RE = re.compile(
    r"(?m)^\s*(?:axiom|opaque)\b|\bsorry\b|\badmit\b|\bnative_decide\b|\bunsafe\b"
)
GENERIC_CACHE_MARKERS = (
    "aesop",
    "(by first |",
    "by assumption",
    "simp (",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def canonical_json_sha256(value: object) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return sha256_bytes(payload)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def safe(label: str) -> str:
    result = re.sub(r"[^A-Za-z0-9_]", "_", label)
    return "n_" + result if not result or result[0].isdigit() else result


def blocks_from_text(text: str, footer_at: int) -> list[tuple[str, str]]:
    matches = list(START_RE.finditer(text[:footer_at]))
    blocks: list[tuple[str, str]] = []
    for index, match in enumerate(matches):
        stop = matches[index + 1].start() if index + 1 < len(matches) else footer_at
        blocks.append((match.group(1), text[match.start() : stop]))
    return blocks


def theorem_statement(block: str) -> str:
    marker = ":= by"
    position = block.find(marker)
    require(position >= 0, "theorem body marker missing")
    return block[: position + len(marker)]


def proof_suffix(block: str) -> str:
    marker = "\n  have p0000 :="
    position = block.find(marker)
    if position >= 0:
        return block[position:]
    marker = "\n  exact "
    position = block.rfind(marker)
    require(position >= 0, "proof suffix missing")
    return block[position:]


def pre_cache_prefix(block: str) -> str:
    match = CACHE_RE.search(block)
    suffix = proof_suffix(block)
    if match is None:
        return block[: block.find(suffix)]
    return block[: match.start()]


def reconstruct_new_parts(
    resource: dict[str, object],
) -> tuple[list[tuple[str, str]], bytes]:
    parts = resource["parts"]
    require(isinstance(parts, list) and len(parts) == NEW_PART_COUNT, "new part count changed")
    blocks: list[tuple[str, str]] = []
    aggregate = bytearray()
    for index, row in enumerate(parts, start=1):
        require(isinstance(row, dict), f"new part record malformed: {index}")
        require(row.get("part") == index, f"new part ordinal changed: {index}")
        path = Path(str(row["source"]))
        require(path.is_file(), f"new part source missing: {path}")
        require(
            path.stat().st_size == row["sourceBytes"]
            and sha256(path) == row["sourceSha256"],
            f"new part source identity changed: {index}",
        )
        predecessor = (
            "NominalWPPReplayChunk010Compact001"
            if index == 1
            else str(parts[index - 2]["module"])
        )
        require(row["predecessor"] == predecessor, "new import-chain record changed")
        text = path.read_text(encoding="utf-8")
        require(
            text.count(f"import {predecessor}\n") == 1,
            f"new import chain changed: {index}",
        )
        require(FORBIDDEN_RE.search(text) is None, f"forbidden new source token: {index}")
        footer = text.rfind("#print axioms g_")
        require(footer > 0, f"new part footer missing: {index}")
        part_blocks = blocks_from_text(text, footer)
        require(len(part_blocks) == row["theoremCount"], "new part theorem count changed")
        copied = "".join(block for _label, block in part_blocks).encode("utf-8")
        require(
            len(copied) == row["copiedTheoremBytes"]
            and sha256_bytes(copied) == row["copiedTheoremSha256"],
            f"new copied theorem bytes changed: {index}",
        )
        require(
            not row["oversizedSingleton"] or row["theoremCount"] == 1,
            f"new oversized nonsingleton: {index}",
        )
        require(
            row["oversizedSingleton"] or row["copiedTheoremBytes"] <= 60_000,
            f"new ordinary part exceeds 60KB: {index}",
        )
        blocks.extend(part_blocks)
        aggregate.extend(copied)
    return blocks, bytes(aggregate)


def reconstruct_old_parts(
    split_resource: dict[str, object],
) -> tuple[list[tuple[str, str]], bytes]:
    parts = split_resource["parts"]
    require(isinstance(parts, list) and len(parts) == OLD_PART_COUNT, "old part count changed")
    blocks: list[tuple[str, str]] = []
    aggregate = bytearray()
    for index, row in enumerate(parts, start=1):
        require(isinstance(row, dict), f"old part record malformed: {index}")
        require(row.get("part") == index, f"old part ordinal changed: {index}")
        path = Path(str(row["source"]))
        require(path.is_file(), f"old part source missing: {path}")
        require(
            path.stat().st_size == row["source_bytes"]
            and sha256(path) == row["source_sha256"],
            f"old part source identity changed: {index}",
        )
        predecessor = (
            "NominalWPPReplayChunk010"
            if index == 1
            else str(parts[index - 2]["module"])
        )
        require(row["predecessor"] == predecessor, "old import-chain record changed")
        text = path.read_text(encoding="utf-8")
        require(
            text.count(f"import {predecessor}\n") == 1,
            f"old import chain changed: {index}",
        )
        require(FORBIDDEN_RE.search(text) is None, f"forbidden old source token: {index}")
        footer = text.rfind("\n\n#print axioms g_")
        require(footer > 0, f"old part footer missing: {index}")
        part_blocks = blocks_from_text(text, footer)
        require(len(part_blocks) == row["theorem_count"], "old part theorem count changed")
        copied = "".join(block for _label, block in part_blocks).encode("utf-8")
        require(
            len(copied) == row["copied_theorem_bytes"]
            and sha256_bytes(copied) == row["theorem_body_sha256"],
            f"old copied theorem bytes changed: {index}",
        )
        require(
            not row["oversized_singleton"] or row["theorem_count"] == 1,
            f"old oversized nonsingleton: {index}",
        )
        require(
            row["oversized_singleton"] or row["copied_theorem_bytes"] <= 60_000,
            f"old ordinary part exceeds 60KB: {index}",
        )
        blocks.extend(part_blocks)
        aggregate.extend(copied)
    return blocks, bytes(aggregate)


def main() -> None:
    started = time.perf_counter()
    require(not OUTPUT.exists(), f"refusing to overwrite append-only audit: {OUTPUT}")
    for path, digest in PINNED.items():
        require(path.is_file(), f"pinned input missing: {path}")
        require(sha256(path) == digest, f"pinned input changed: {path}")

    resource = json.loads(NEW_RESOURCE.read_text(encoding="utf-8"))
    source_audit = json.loads(NEW_SOURCE_AUDIT.read_text(encoding="utf-8"))
    manifest = json.loads(OLD_MANIFEST.read_text(encoding="utf-8"))
    old_source_audit = json.loads(OLD_SOURCE_AUDIT.read_text(encoding="utf-8"))
    old_split = json.loads(OLD_SPLIT.read_text(encoding="utf-8"))
    old_split_audit = json.loads(OLD_SPLIT_AUDIT.read_text(encoding="utf-8"))

    require(
        resource.get("status") == "PASS_SOURCE_ONLY_EMITTED_STRUCTURAL"
        and resource.get("leanStartedByThisProducer") is False
        and resource.get("startTheoremOrdinal") == START_ORDINAL
        and resource.get("endTheoremOrdinal") == END_ORDINAL
        and resource.get("theoremCount") == THEOREM_COUNT
        and resource.get("partCount") == NEW_PART_COUNT
        and resource.get("maximumCopiedTheoremBytes") == 60_000
        and resource.get("aggregateTheoremBytes") == NEW_AGGREGATE_BYTES
        and resource.get("aggregateTheoremSha256") == NEW_AGGREGATE_SHA256
        and resource.get("applicationCount") == APPLICATION_COUNT
        and resource.get("applicationTraceSha256") == TRACE_SHA256
        and resource.get("structuralCertificateCensus")
        == {
            "total": CACHE_COUNT,
            "nonmembership": NONMEMBERSHIP_COUNT,
            "inequality": INEQUALITY_COUNT,
            "disjoint": 0,
        }
        and resource.get("compactFvNormalizationCount") == NONMEMBERSHIP_COUNT
        and resource.get("genericDvFallbackCount") == 0,
        "new compact resource contract changed",
    )
    require(
        resource.get("producer", {}).get("sha256") == PINNED[TRANSLATOR]
        and resource.get("compactFvNormalizationBackend", {}).get("moduleSha256")
        == PINNED[MIXIN]
        and resource.get("compactFvNormalizationBackend", {}).get("alphaNeutral")
        is True,
        "translator/compact-backend provenance changed",
    )
    require(
        resource.get("predecessor", {}).get("resourceSha256") == PINNED[PREDECESSOR]
        and resource.get("predecessor", {}).get("endTheoremOrdinal") == 2504
        and resource.get("predecessor", {}).get("module")
        == "NominalWPPReplayChunk010Compact001"
        and resource.get("predecessor", {}).get("boundaryKind") == "source-only"
        and resource.get("alphaFrontier", {}).get("resourceSha256") == PINNED[ALPHA48]
        and resource.get("alphaFrontier", {}).get("endOrdinal") == 48,
        "predecessor/alpha boundary changed",
    )
    require(
        resource.get("umbrellaModule", {}).get("module")
        == "NominalWPPReplayChunk011Compact001"
        and resource.get("umbrellaModule", {}).get("sourceSha256")
        == NEW_UMBRELLA_SHA256,
        "new compatibility umbrella changed",
    )
    require(
        source_audit.get("checks", {}).get("allNonmembershipCachesCompactNormalized")
        is True
        and source_audit.get("checks", {}).get("allTheoremBodiesPartitionedByteExactly")
        is True
        and source_audit.get("checks", {}).get("allNonSingletonPartsWithinByteLimit")
        is True
        and source_audit.get("checks", {}).get("allOversizedPartsAreSingletons")
        is True
        and source_audit.get("checks", {}).get("genericDvFallbackCountZero") is True
        and source_audit.get("checks", {}).get("forbiddenGeneratedTokensAbsent") is True,
        "built-in new source audit lost a required check",
    )
    require(
        old_source_audit.get("status") == "PASS_SOURCE_ONLY_EXACT_REVERSIBLE_FULL_CHUNK"
        and old_split.get("status") == "GENERATED_SOURCE_ONLY_EXACT_REVERSIBLE_CHAINED_SPLIT"
        and old_split_audit.get("status")
        == "PASS_SOURCE_ONLY_EXACT_REVERSIBLE_CHAINED_SPLIT"
        and old_split_audit.get("checks", {}).get("sourceReconstructionByteExact")
        is True,
        "accepted old chunk-11 boundary changed",
    )
    require(
        manifest.get("theorem_count") == THEOREM_COUNT
        and manifest.get("proof_op_count") == PROOF_OP_COUNT
        and manifest.get("application_count") == APPLICATION_COUNT
        and len(manifest.get("trace", [])) == APPLICATION_COUNT,
        "accepted old source/trace census changed",
    )

    new_blocks, new_aggregate = reconstruct_new_parts(resource)
    require(len(new_blocks) == THEOREM_COUNT, "new reconstructed theorem count changed")
    require(
        len(new_aggregate) == NEW_AGGREGATE_BYTES
        and sha256_bytes(new_aggregate) == NEW_AGGREGATE_SHA256,
        "new aggregate theorem reconstruction changed",
    )

    old_split_blocks, old_split_aggregate = reconstruct_old_parts(old_split)
    require(len(old_split_blocks) == THEOREM_COUNT, "old split theorem count changed")
    require(
        len(old_split_aggregate) == OLD_AGGREGATE_BYTES
        and sha256_bytes(old_split_aggregate) == OLD_AGGREGATE_SHA256,
        "old split aggregate reconstruction changed",
    )
    old_text = OLD_SOURCE.read_text(encoding="utf-8")
    old_footer = old_text.rfind("\n\n#print axioms g_f1oeq2")
    require(old_footer > 0, "accepted chunk-11 footer missing")
    old_blocks = blocks_from_text(old_text, old_footer)
    require(len(old_blocks) == THEOREM_COUNT, "accepted old theorem count changed")
    require(
        old_split_blocks == old_blocks
        and old_split_aggregate
        == "".join(block for _label, block in old_blocks).encode("utf-8"),
        "old split does not reversibly reconstruct accepted old source",
    )

    expected_labels = list(manifest["labels"])
    expected_safe_labels = [safe(label) for label in expected_labels]
    require(
        [label for label, _block in old_blocks]
        == [label for label, _block in new_blocks]
        == expected_safe_labels,
        "old/new theorem label sequence changed",
    )
    theorem_rows = source_audit["theorems"]
    require(len(theorem_rows) == THEOREM_COUNT, "new theorem audit row count changed")
    expected_trace_by_label: dict[str, list[dict[str, object]]] = {
        label: [] for label in expected_labels
    }
    for trace_row in manifest["trace"]:
        expected_trace_by_label[trace_row["theorem"]].append(trace_row)
    require(
        canonical_json_sha256(manifest["trace"]) == TRACE_SHA256,
        "accepted aggregate trace differs from new compact trace",
    )

    statement_matches = 0
    prelude_matches = 0
    cache_target_matches = 0
    proof_suffix_matches = 0
    trace_matches = 0
    proof_ops_matches = 0
    compact_markers = 0
    cache_total = 0
    cache_nonmembership = 0
    cache_inequality = 0
    for offset, ((old_label, old_block), (new_label, new_block), row, raw_label) in enumerate(
        zip(old_blocks, new_blocks, theorem_rows, expected_labels, strict=True)
    ):
        require(
            old_label == new_label == row["safeName"] == safe(raw_label),
            f"safe label mismatch: {raw_label}",
        )
        require(row["ordinal"] == START_ORDINAL + offset, "theorem ordinal changed")
        require(
            row["proofOpsSha256"] == manifest["proof_ops_sha256"][raw_label],
            f"proof-op hash changed: {raw_label}",
        )
        proof_ops_matches += 1
        expected_trace = expected_trace_by_label[raw_label]
        require(
            row["applicationCount"] == len(expected_trace)
            and row["applicationTraceSha256"]
            == canonical_json_sha256(expected_trace),
            f"application/substitution/dependency trace changed: {raw_label}",
        )
        trace_matches += 1
        require(
            theorem_statement(old_block) == theorem_statement(new_block),
            f"theorem statement changed: {raw_label}",
        )
        statement_matches += 1
        require(
            pre_cache_prefix(old_block) == pre_cache_prefix(new_block),
            f"statement/pre-cache prelude changed: {raw_label}",
        )
        prelude_matches += 1
        old_caches = CACHE_RE.findall(old_block)
        new_caches = CACHE_RE.findall(new_block)
        require(old_caches == new_caches, f"DV cache targets changed: {raw_label}")
        cache_target_matches += 1
        cache_total += len(new_caches)
        cache_nonmembership += sum(" ∉ " in target for _name, target in new_caches)
        cache_inequality += sum(" ≠ " in target for _name, target in new_caches)
        require(
            proof_suffix(old_block).rstrip("\n")
            == proof_suffix(new_block).rstrip("\n"),
            f"proof-DAG suffix changed: {raw_label}",
        )
        proof_suffix_matches += 1

        matches = list(CACHE_RE.finditer(new_block))
        suffix_start = new_block.find(proof_suffix(new_block))
        for cache_index, match in enumerate(matches):
            end = matches[cache_index + 1].start() if cache_index + 1 < len(matches) else suffix_start
            region = new_block[match.start() : end]
            target = match.group(2)
            require(
                all(marker not in region for marker in GENERIC_CACHE_MARKERS),
                f"generic cache fallback escaped: {raw_label}/{match.group(1)}",
            )
            marker_count = region.count("have compact_fv_not_mem_empty")
            if " ∉ " in target:
                require(
                    marker_count == 1,
                    f"nonmembership cache is not compact-normalized: {raw_label}/{match.group(1)}",
                )
                compact_markers += marker_count
            else:
                require(
                    marker_count == 0,
                    f"compact nonmembership marker escaped into other cache: {raw_label}/{match.group(1)}",
                )

    require(
        cache_total == CACHE_COUNT
        and cache_nonmembership == NONMEMBERSHIP_COUNT
        and cache_inequality == INEQUALITY_COUNT
        and compact_markers == NONMEMBERSHIP_COUNT,
        "cache/compact census changed",
    )

    oversized = [row for row in resource["parts"] if row["oversizedSingleton"]]
    require(
        len(oversized) == 1
        and oversized[0]["part"] == 13
        and oversized[0]["startTheoremOrdinal"] == 2672
        and oversized[0]["firstLabel"] == "fununi",
        "new oversized-singleton census changed",
    )
    output = {
        "schema": "nf-reusable-nominal-mm-translator-v1-chunk011-compact-source-audit-v1",
        "status": "PASS_SOURCE_ONLY_EXACT_REVERSIBLE_COMPACT_CHUNK011",
        "leanStartedByThisAudit": False,
        "producer": str(THIS),
        "producerSha256": sha256(THIS),
        "pinnedInputs": {str(path): digest for path, digest in PINNED.items()},
        "sourceResource": str(NEW_RESOURCE),
        "sourceResourceSha256": PINNED[NEW_RESOURCE],
        "sourceAudit": str(NEW_SOURCE_AUDIT),
        "sourceAuditSha256": PINNED[NEW_SOURCE_AUDIT],
        "acceptedOldSource": str(OLD_SOURCE),
        "acceptedOldSourceSha256": PINNED[OLD_SOURCE],
        "acceptedOldManifest": str(OLD_MANIFEST),
        "acceptedOldManifestSha256": PINNED[OLD_MANIFEST],
        "startTheoremOrdinal": START_ORDINAL,
        "endTheoremOrdinal": END_ORDINAL,
        "theoremCount": THEOREM_COUNT,
        "newPartCount": NEW_PART_COUNT,
        "oldPartCount": OLD_PART_COUNT,
        "oversizedSingletonCount": len(oversized),
        "oversizedSingletons": [
            {
                "part": row["part"],
                "ordinal": row["startTheoremOrdinal"],
                "label": row["firstLabel"],
                "copiedTheoremBytes": row["copiedTheoremBytes"],
                "sourceSha256": row["sourceSha256"],
            }
            for row in oversized
        ],
        "newAggregateTheoremBytes": len(new_aggregate),
        "newAggregateTheoremSha256": NEW_AGGREGATE_SHA256,
        "oldAggregateTheoremBytes": len(old_split_aggregate),
        "oldAggregateTheoremSha256": OLD_AGGREGATE_SHA256,
        "applicationCount": APPLICATION_COUNT,
        "applicationTraceSha256": TRACE_SHA256,
        "cacheCount": CACHE_COUNT,
        "nonmembershipCacheCount": NONMEMBERSHIP_COUNT,
        "inequalityCacheCount": INEQUALITY_COUNT,
        "compactFvNormalizationCount": compact_markers,
        "statementExactMatchCount": statement_matches,
        "preludeExactMatchCount": prelude_matches,
        "cacheTargetsExactMatchCount": cache_target_matches,
        "proofDagSuffixExactModuloTrailingLfCount": proof_suffix_matches,
        "proofOpsExactMatchCount": proof_ops_matches,
        "applicationTraceExactMatchCount": trace_matches,
        "newSplitReconstructionExact": True,
        "oldSplitReconstructionExact": True,
        "allNonmembershipCachesCompactNormalized": True,
        "genericCacheFallbackCount": 0,
        "forbiddenGeneratedSourceTokenCount": 0,
        "auditElapsedSeconds": round(time.perf_counter() - started, 6),
    }
    OUTPUT.mkdir(parents=True, exist_ok=False)
    OUTPUT_RESOURCE.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
