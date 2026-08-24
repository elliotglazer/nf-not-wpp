#!/usr/bin/env python3
"""Independent reversible audit of reusable compact chunk10 source.

No Lean process is started.  The audit pins both the accepted structural
chunk10 and the fresh reusable-CLI compact successor, reconstructs every
theorem block from the chained split, and proves exact preservation of labels,
statements/preludes, DV-cache targets, proof programs, proof-DAG suffixes, and
all application/substitution/dependency traces.  It additionally compares the
pathological ``nnadjoinlem1`` block byte-for-byte with the separately generated
frontier48 compact golden probe.
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
NEW = HERE / "reusable_nominal_mm_translator_v1_chunk010_compact_001"
NEW_RESOURCE = NEW / "resource.json"
NEW_SOURCE_AUDIT = NEW / "source_audit.json"
OLD = HERE / "generated_nominal_wpp_replay_prefix48_cached_structural_fv_chunk010_001"
OLD_SOURCE = OLD / "NominalWPPReplayChunk010.lean"
OLD_MANIFEST = OLD / "nominal_wpp_replay_chunk_010_manifest.json"
OLD_SOURCE_AUDIT = (
    HERE / "nominal_wpp_prefix48_cached_structural_fv_chunk010_source_audit_001"
    / "resource.json"
)
GOLDEN = (
    HERE / "generated_nominal_wpp_compact_normalize_nnadjoinlem1_001"
    / "NominalWPPReplayChunk010StructuralPart008.lean"
)
GOLDEN_RESOURCE = (
    HERE / "generated_nominal_wpp_compact_normalize_nnadjoinlem1_001"
    / "resource.json"
)
PREDECESSOR = HERE / "c9i003" / "resource.json"
ALPHA48 = HERE / "a3848k1" / "resource.json"
OUTPUT = (
    HERE / "reusable_nominal_mm_translator_v1_chunk010_compact_source_audit_001"
)
OUTPUT_RESOURCE = OUTPUT / "resource.json"

PINNED = {
    TRANSLATOR: "12A59CDC12DE5F10DCD20D3479F7DD4DB57623B4E3FCBFCA70FE82A515E57F85",
    MIXIN: "CA7493053B75FC9B2EDC0F6C16AE31DE07C5F1A52119F15314BD09D3A165BDA4",
    NEW_RESOURCE: "3F2C7D736EBF7D92BE136362E81AEDDE0259433BE4DEE0631DE3B2E29330DB7A",
    NEW_SOURCE_AUDIT: "7C1A16AE304132502A7142CDDA0506684D0C0D0920E25B797EF00CE5331E04BD",
    OLD_SOURCE: "BF6C1437EDC65348BF39B9C3A3DAC642E67C6219151C20DEFC36EB9051BCC448",
    OLD_MANIFEST: "00250AA093B05F75D2A4A72A52B69B2885BEF9E0A536EE2A76EBCF9A3DF1F7BB",
    OLD_SOURCE_AUDIT: "FF6C76258B2403129ED25C061186B87C39C47F9FAD5C15AAECD68E9514FE68C2",
    GOLDEN: "8ACAB62D3E95009D26F64C923E5E418E7879213DEB6958989852815FC8A40751",
    GOLDEN_RESOURCE: "B0FB368E6C9EBBBD49A6F14B71C63915E5917AD93C607E8E2D296E208938419F",
    PREDECESSOR: "8215DF3B100FD72809AD95350ED957369989126A3E3B7F17E7C4134118AE69DD",
    ALPHA48: "5299F0DA88C07150FCEBB96F2C04CC0DCDFF6C3FC48265C65BA407BC8DBC9FCA",
}

START_ORDINAL = 2255
END_ORDINAL = 2504
THEOREM_COUNT = 250
APPLICATION_COUNT = 6565
CACHE_COUNT = 1975
NONMEMBERSHIP_COUNT = 1712
INEQUALITY_COUNT = 263
PART_COUNT = 66
AGGREGATE_SHA256 = "DD11F629EF374E76A65379227DA75C8EEED59AF2F9623E6EB79F66C39D462B64"
TRACE_SHA256 = "938A704E85096BE1A1C8879B7152159288E927A2A4BA20BAA40C1B739B82D42E"

START_RE = re.compile(r"(?m)^noncomputable def g_([A-Za-z0-9_]+)\b")
CACHE_RE = re.compile(r"(?m)^  have (dv_cache_[0-9]+) : (.+) := by$")
FORBIDDEN_RE = re.compile(
    r"(?m)^\s*(?:axiom|opaque)\b|\bsorry\b|\badmit\b|\bnative_decide\b|\bunsafe\b"
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
    result: list[tuple[str, str]] = []
    for index, match in enumerate(matches):
        stop = matches[index + 1].start() if index + 1 < len(matches) else footer_at
        result.append((match.group(1), text[match.start():stop]))
    return result


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
    if match is None:
        return block[: block.find(proof_suffix(block))]
    return block[:match.start()]


def main() -> None:
    started = time.perf_counter()
    require(not OUTPUT.exists(), f"refusing to overwrite append-only audit: {OUTPUT}")
    for path, digest in PINNED.items():
        require(path.is_file(), f"pinned input missing: {path}")
        require(sha256(path) == digest, f"pinned input changed: {path}")

    resource = json.loads(NEW_RESOURCE.read_text(encoding="utf-8"))
    source_audit = json.loads(NEW_SOURCE_AUDIT.read_text(encoding="utf-8"))
    manifest = json.loads(OLD_MANIFEST.read_text(encoding="utf-8"))
    golden_resource = json.loads(GOLDEN_RESOURCE.read_text(encoding="utf-8"))
    require(
        resource.get("status") == "PASS_SOURCE_ONLY_EMITTED_STRUCTURAL"
        and resource.get("leanStartedByThisProducer") is False
        and resource.get("startTheoremOrdinal") == START_ORDINAL
        and resource.get("endTheoremOrdinal") == END_ORDINAL
        and resource.get("theoremCount") == THEOREM_COUNT
        and resource.get("partCount") == PART_COUNT
        and resource.get("maximumCopiedTheoremBytes") == 60_000
        and resource.get("aggregateTheoremSha256") == AGGREGATE_SHA256
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
        "compact resource contract changed",
    )
    require(
        resource.get("producer", {}).get("sha256") == PINNED[TRANSLATOR]
        and resource.get("compactFvNormalizationBackend", {}).get("moduleSha256")
        == PINNED[MIXIN]
        and resource.get("compactFvNormalizationBackend", {}).get("alphaNeutral")
        is True,
        "translator/mixin provenance changed",
    )
    require(
        source_audit.get("checks", {}).get(
            "allNonmembershipCachesCompactNormalized"
        ) is True
        and source_audit.get("checks", {}).get(
            "allTheoremBodiesPartitionedByteExactly"
        ) is True
        and source_audit.get("checks", {}).get("genericDvFallbackCountZero")
        is True,
        "built-in source audit lost a required check",
    )

    parts = resource["parts"]
    require(len(parts) == PART_COUNT, "part count changed")
    new_blocks: list[tuple[str, str]] = []
    reconstructed = bytearray()
    for index, row in enumerate(parts, start=1):
        require(row.get("part") == index, f"part ordinal changed: {index}")
        path = Path(row["source"])
        require(path.is_file(), f"part source missing: {path}")
        require(
            path.stat().st_size == row["sourceBytes"]
            and sha256(path) == row["sourceSha256"],
            f"part source identity changed: {index}",
        )
        expected_predecessor = (
            "NominalWPPReplayChunk009"
            if index == 1
            else parts[index - 2]["module"]
        )
        require(row["predecessor"] == expected_predecessor, "import-chain record changed")
        text = path.read_text(encoding="utf-8")
        require(
            text.count(f"import {expected_predecessor}\n") == 1,
            f"part import chain changed: {index}",
        )
        require(FORBIDDEN_RE.search(text) is None, f"forbidden source token: part {index}")
        footer = text.rfind("#print axioms g_")
        require(footer > 0, f"part footer missing: {index}")
        part_blocks = blocks_from_text(text, footer)
        require(len(part_blocks) == row["theoremCount"], "part theorem count changed")
        copied = "".join(block for _label, block in part_blocks).encode("utf-8")
        require(
            len(copied) == row["copiedTheoremBytes"]
            and sha256_bytes(copied) == row["copiedTheoremSha256"],
            f"copied theorem bytes changed: part {index}",
        )
        require(
            not row["oversizedSingleton"] or row["theoremCount"] == 1,
            f"oversized nonsingleton: part {index}",
        )
        require(
            row["oversizedSingleton"]
            or row["copiedTheoremBytes"] <= 60_000,
            f"ordinary part exceeds limit: {index}",
        )
        new_blocks.extend(part_blocks)
        reconstructed.extend(copied)

    require(len(new_blocks) == THEOREM_COUNT, "reconstructed theorem count changed")
    require(
        len(reconstructed) == resource["aggregateTheoremBytes"]
        and sha256_bytes(bytes(reconstructed)) == AGGREGATE_SHA256,
        "aggregate theorem reconstruction changed",
    )

    old_text = OLD_SOURCE.read_text(encoding="utf-8")
    old_footer = old_text.rfind("\n\n#print axioms g_coeq1i")
    require(old_footer > 0, "accepted chunk10 footer missing")
    old_blocks = blocks_from_text(old_text, old_footer)
    require(len(old_blocks) == THEOREM_COUNT, "accepted theorem count changed")
    expected_labels = list(manifest["labels"])
    expected_safe_labels = [safe(label) for label in expected_labels]
    require(
        [label for label, _block in old_blocks]
        == [label for label, _block in new_blocks]
        == expected_safe_labels,
        "label sequence changed",
    )

    theorem_rows = source_audit["theorems"]
    require(len(theorem_rows) == THEOREM_COUNT, "audit theorem row count changed")
    expected_trace_by_label: dict[str, list[dict[str, object]]] = {
        label: [] for label in expected_labels
    }
    for row in manifest["trace"]:
        expected_trace_by_label[row["theorem"]].append(row)
    require(
        canonical_json_sha256(manifest["trace"]) == TRACE_SHA256,
        "accepted aggregate trace differs from compact trace",
    )

    statement_matches = 0
    prelude_matches = 0
    cache_target_matches = 0
    proof_suffix_matches = 0
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
        expected_trace = expected_trace_by_label[raw_label]
        require(
            row["applicationCount"] == len(expected_trace)
            and row["applicationTraceSha256"]
            == canonical_json_sha256(expected_trace),
            f"application/substitution/dependency trace changed: {raw_label}",
        )
        require(theorem_statement(old_block) == theorem_statement(new_block),
                f"statement changed: {raw_label}")
        statement_matches += 1
        require(pre_cache_prefix(old_block) == pre_cache_prefix(new_block),
                f"statement/prelude changed: {raw_label}")
        prelude_matches += 1
        old_caches = CACHE_RE.findall(old_block)
        new_caches = CACHE_RE.findall(new_block)
        require(old_caches == new_caches, f"cache targets changed: {raw_label}")
        cache_target_matches += 1
        cache_total += len(new_caches)
        cache_nonmembership += sum(" ∉ " in target for _name, target in new_caches)
        cache_inequality += sum(" ≠ " in target for _name, target in new_caches)
        require(
            proof_suffix(old_block).rstrip("\n")
            == proof_suffix(new_block).rstrip("\n"),
                f"proof-DAG suffix changed: {raw_label}")
        proof_suffix_matches += 1
        compact_markers += new_block.count("have compact_fv_not_mem_empty")
        if new_caches:
            cache_start = CACHE_RE.search(new_block)
            assert cache_start is not None
            suffix_start = new_block.find(proof_suffix(new_block))
            cache_region = new_block[cache_start.start():suffix_start]
            require(
                "aesop" not in cache_region
                and "(by first |" not in cache_region
                and "by assumption" not in cache_region
                and "simp (" not in cache_region,
                f"generic cache proof escaped: {raw_label}",
            )

    require(
        cache_total == CACHE_COUNT
        and cache_nonmembership == NONMEMBERSHIP_COUNT
        and cache_inequality == INEQUALITY_COUNT
        and compact_markers == NONMEMBERSHIP_COUNT,
        "cache/compact census changed",
    )

    golden_text = GOLDEN.read_text(encoding="utf-8")
    golden_start = golden_text.index("noncomputable def g_nnadjoinlem1")
    golden_end = golden_text.index("\n\n#print axioms g_nnadjoinlem1", golden_start)
    golden_theorem = golden_text[golden_start:golden_end]
    compact_nnadjoin = dict(new_blocks)["nnadjoinlem1"].removesuffix("\n\n")
    require(compact_nnadjoin == golden_theorem, "reusable nnadjoinlem1 differs from golden")
    require(
        sha256_bytes(compact_nnadjoin.encode("utf-8"))
        == golden_resource["new_theorem_sha256"],
        "golden nnadjoinlem1 digest changed",
    )

    oversized = [row for row in parts if row["oversizedSingleton"]]
    output = {
        "schema": "nf-reusable-nominal-mm-translator-v1-chunk010-compact-source-audit-v1",
        "status": "PASS_SOURCE_ONLY_EXACT_REVERSIBLE_COMPACT_CHUNK010",
        "leanStartedByThisAudit": False,
        "producer": str(THIS),
        "producerSha256": sha256(THIS),
        "pinnedInputs": {str(path): digest for path, digest in PINNED.items()},
        "sourceResource": str(NEW_RESOURCE),
        "sourceResourceSha256": PINNED[NEW_RESOURCE],
        "sourceAudit": str(NEW_SOURCE_AUDIT),
        "sourceAuditSha256": PINNED[NEW_SOURCE_AUDIT],
        "startTheoremOrdinal": START_ORDINAL,
        "endTheoremOrdinal": END_ORDINAL,
        "theoremCount": THEOREM_COUNT,
        "partCount": PART_COUNT,
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
        "aggregateTheoremBytes": len(reconstructed),
        "aggregateTheoremSha256": AGGREGATE_SHA256,
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
        "proofOpsExactMatchCount": THEOREM_COUNT,
        "applicationTraceExactMatchCount": THEOREM_COUNT,
        "nnadjoinlem1GoldenExactMatch": True,
        "genericCacheFallbackCount": 0,
        "forbiddenGeneratedSourceTokenCount": 0,
        "generationElapsedSeconds": round(time.perf_counter() - started, 6),
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
