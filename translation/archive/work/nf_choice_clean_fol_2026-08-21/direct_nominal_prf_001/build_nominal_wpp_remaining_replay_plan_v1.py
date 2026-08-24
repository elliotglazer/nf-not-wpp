#!/usr/bin/env python3
"""Build the deterministic post-alpha97 NF/WPP theorem-replay plan.

This planner is deliberately source-only.  It proof-checks the exact repaired
Metamath database, replays the endpoint AST, and records the remaining theorem
interval.  It neither accepts an alpha frontier nor starts Lean; the separate
runner refuses to translate until an exact-three trust-zero alpha97 resource
is supplied.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


HERE = Path(__file__).resolve().parent
WORK = HERE.parents[1]
COMPILER = HERE.parent / "compiler"

SOURCE = (
    WORK
    / "mm0_conversion_2026-08-20"
    / "source_repair"
    / "hnwcut_resisomr_assist"
    / "endpoint_after_hnwcut_alias0_scope_repaired_mm0_importer_clean.mm"
)
SOURCE_SHA256 = "868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F"
SOURCE_BYTES = 9_945_323
ENDPOINT = "wppfiniteblocknotwppndv"
ENDPOINT_AST = "(wn wwpp)"
ENDPOINT_EXPRESSION = ("|-", "-.", "WPP")
CLOSURE_ASSERTION_COUNT = 4_912
CLOSURE_THEOREM_COUNT = 4_321

RELEASE_MANIFEST = HERE / "translator_release_nf_wpp_002" / "manifest.json"
RELEASE_MANIFEST_SHA256 = (
    "2D36471B4AC27200AE0226E63FDCC834FAFF8DD95AD71C9062B7B7B27DBFAF7F"
)
RELEASE_AUDIT = HERE / "translator_release_nf_wpp_002_audit_001" / "resource.json"
RELEASE_AUDIT_SHA256 = (
    "D0DAB31A13028465F56ED6B0D40691F4CD271478BF60F278B8A2D4DA042E8550"
)
TRANSLATOR = HERE / "reusable_nominal_mm_translator_v1.py"
TRANSLATOR_SHA256 = (
    "8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94"
)
PROFILE = HERE / "WPP_PROFILE_V2.json"
PROFILE_SHA256 = (
    "96B6A85D4B5B60023000C49BB40CF4F7DCD679AAF4DB6C796880A684DBF12949"
)

PREDECESSOR_RESOURCE = HERE / "k12ag002" / "resource.json"
PREDECESSOR_RESOURCE_SHA256 = (
    "EC9375ABE945791CECD7B4D5E48A07545B54042753D7C1A14258EC28AD041345"
)
PREDECESSOR_SOURCE_RESOURCE_SHA256 = (
    "7C3B50C8208C309E411091BF9EBA887CE42289C80C71E7C890AE4EFABAB94D11"
)
PREDECESSOR_SOURCE_AUDIT = (
    HERE
    / "reusable_nominal_mm_translator_v1_chunk012a_compact_002"
    / "source_audit.json"
)
PREDECESSOR_SOURCE_AUDIT_SHA256 = (
    "46D1AD16320A56BE3C56FA45EF23981B1B3E42A8D21A9C35AD05AFDBB9C18F83"
)
PREDECESSOR_MODULE = "NominalWPPReplayChunk012ACompact002"
PREDECESSOR_END_ORDINAL = 2_866
PREDECESSOR_LAST_LABEL = "f1ocnvdm"

MM_PARSER = COMPILER / "mm_parser.py"
MM_PARSER_SHA256 = (
    "D657F2FCA96CDFFD8E61FA2845A324CFBCC18777A48A817B8D718280A005C4B7"
)
AST_REPLAY = COMPILER / "ast_replay.py"
AST_REPLAY_SHA256 = (
    "BB7875EC606128B40307D42EE1919A341E31B88F57DD0AB032CCD2C849C22ADF"
)
SYNTAX = COMPILER / "syntax.py"
SYNTAX_SHA256 = (
    "216445BC60A6B50906AB862BD2221F846B2B6D071A74A1280F62227CAEAC9618"
)

SPLIT_BYTES = 60_000
NAMESPACE = "NFChoice.DirectNominalPrf.WPPReplay"
REMAINING_START = 2_867
REMAINING_END = 4_321

# This continues the already-established 250-theorem logical chunks.  Chunk
# 012A stopped at the alpha49 frontier, so 012B is the rest of logical chunk
# 12; chunks 13--17 contain 250 theorems and chunk 18 ends at the endpoint.
CHUNK_SPECS = (
    ("012B", 2_867, 3_004),
    ("013", 3_005, 3_254),
    ("014", 3_255, 3_504),
    ("015", 3_505, 3_754),
    ("016", 3_755, 4_004),
    ("017", 4_005, 4_254),
    ("018", 4_255, 4_321),
)

EXPECTED_BOUNDARIES = {
    "012B": ("isoeq1", "brdisjg"),
    "013": ("brdisj", "freceq12"),
    "014": ("frecexg", "kqfinsucnle"),
    "015": ("kqfinantinn", "wecutisocompatndv"),
    "016": ("wecutisosamesourcendv", "siorreflectndv"),
    "017": ("sifrreflectndv", "cfbwppfixedblockhnqgraphinjndv"),
    "018": ("cfbhncardpowershiftndv", "wppfiniteblocknotwppndv"),
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_json_sha256(value: object) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return sha256_bytes(payload)


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=False) + "\n").encode("utf-8")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def require_hash(path: Path, expected: str, description: str) -> None:
    require(path.is_file(), f"missing {description}: {path}")
    actual = sha256(path)
    require(actual == expected, f"{description} hash mismatch: {actual} != {expected}")


def relative(path: Path) -> str:
    return path.resolve().relative_to(HERE).as_posix()


def workspace_relative(path: Path) -> str:
    return Path(os.path.relpath(path.resolve(), HERE)).as_posix()


def proof_ops_digest(statement: Any) -> str:
    payload = "\n".join(
        f"{op.kind}:{op.value}" for op in statement.proof_ops
    ).encode("utf-8")
    return sha256_bytes(payload)


def verify_release_and_predecessor() -> None:
    require_hash(RELEASE_MANIFEST, RELEASE_MANIFEST_SHA256, "release002 manifest")
    release = json.loads(RELEASE_MANIFEST.read_text(encoding="utf-8"))
    require(release.get("releaseId") == "NF_WPP_TRANSLATOR_TOOLCHAIN_002",
            "unexpected release002 identity")
    require(release.get("translator", {}).get("sha256") == TRANSLATOR_SHA256,
            "release002 translator pin differs")
    require(release.get("scope", {}).get("fullEndpointClaimedByThisRelease") is False,
            "release002 unexpectedly claims the endpoint")
    require_hash(RELEASE_AUDIT, RELEASE_AUDIT_SHA256, "release002 audit")
    audit = json.loads(RELEASE_AUDIT.read_text(encoding="utf-8"))
    require(
        audit.get("status") == "PASS_INDEPENDENT_SOURCE_ONLY_RELEASE002_AUDIT_NO_LEAN",
        "release002 independent audit is not successful",
    )
    require(audit.get("leanStarted") is False,
            "release002 audit does not certify source-only operation")
    require_hash(TRANSLATOR, TRANSLATOR_SHA256, "release002 translator")
    require_hash(PROFILE, PROFILE_SHA256, "WPP profile V2")

    require_hash(
        PREDECESSOR_RESOURCE,
        PREDECESSOR_RESOURCE_SHA256,
        "accepted chunk012A kernel resource",
    )
    predecessor = json.loads(PREDECESSOR_RESOURCE.read_text(encoding="utf-8"))
    require(
        predecessor.get("status")
        == "PASS_TRUST_ZERO_ALL_PARTS_AND_UMBRELLA_EXACT_THREE",
        "chunk012A predecessor is not the accepted exact-three kernel boundary",
    )
    command = predecessor.get("umbrellaCommand")
    require(isinstance(command, Mapping), "chunk012A has no umbrella command")
    require(
        command.get("module") == PREDECESSOR_MODULE
        and command.get("trust") == 0
        and command.get("exitCode") == 0
        and command.get("killed") is False
        and command.get("exactAllowedThree") is True,
        "chunk012A umbrella command does not satisfy the pinned kernel boundary",
    )
    source_ref = predecessor.get("sourceResource")
    require(isinstance(source_ref, Mapping), "chunk012A has no source resource pin")
    require(
        source_ref.get("sha256") == PREDECESSOR_SOURCE_RESOURCE_SHA256,
        "chunk012A source resource pin differs",
    )
    require_hash(
        PREDECESSOR_SOURCE_AUDIT,
        PREDECESSOR_SOURCE_AUDIT_SHA256,
        "accepted chunk012A source audit",
    )
    source_audit = json.loads(PREDECESSOR_SOURCE_AUDIT.read_text(encoding="utf-8"))
    require(
        source_audit.get("status") == "PASS_SOURCE_ONLY_EMITTED_STRUCTURAL"
        and source_audit.get("sourceSha256") == SOURCE_SHA256
        and source_audit.get("endpoint") == ENDPOINT
        and source_audit.get("endpointAst") == ENDPOINT_AST
        and source_audit.get("closureAssertionCount") == CLOSURE_ASSERTION_COUNT
        and source_audit.get("closureProofTheoremCount") == CLOSURE_THEOREM_COUNT,
        "accepted chunk012A source/AST audit differs from the plan pins",
    )


def load_checked_closure() -> tuple[Any, Mapping[str, Any], tuple[str, ...]]:
    require_hash(SOURCE, SOURCE_SHA256, "repaired Metamath source")
    require(SOURCE.stat().st_size == SOURCE_BYTES, "repaired source byte count changed")
    require_hash(MM_PARSER, MM_PARSER_SHA256, "Metamath parser")
    # These are release002 translator backend pins.  The planner does not run
    # the expensive full AST replay a second time: its exact result is imported
    # from the hash-pinned accepted chunk012A source audit above.
    require_hash(AST_REPLAY, AST_REPLAY_SHA256, "release002 AST replayer")
    require_hash(SYNTAX, SYNTAX_SHA256, "release002 syntax grammar")
    if str(COMPILER) not in sys.path:
        sys.path.insert(0, str(COMPILER))
    from mm_parser import Database, tokenize_text  # type: ignore[import-not-found]

    tokens = tokenize_text(SOURCE.read_text(encoding="utf-8"))
    require("$[" not in tokens and "$]" not in tokens,
            "repaired source unexpectedly contains a Metamath include")
    database = Database()
    database.parse(SOURCE)
    require(ENDPOINT in database.statements, "endpoint is absent")
    endpoint = database.statements[ENDPOINT]
    require(endpoint.kind == "$p" and endpoint.typecode == "|-",
            "endpoint is not a proved |- statement")
    require(tuple(endpoint.expr) == ENDPOINT_EXPRESSION,
            "endpoint expression changed")
    replay = json.loads(PREDECESSOR_SOURCE_AUDIT.read_text(encoding="utf-8"))
    labels = tuple(
        statement.label
        for statement in database.dependency_closure(ENDPOINT)
        if statement.kind == "$p" and statement.typecode == "|-"
    )
    require(len(labels) == CLOSURE_THEOREM_COUNT,
            "proved theorem label closure count changed")
    require(labels[-1] == ENDPOINT, "endpoint is not the final closure theorem")
    require(labels[PREDECESSOR_END_ORDINAL - 1] == PREDECESSOR_LAST_LABEL,
            "accepted predecessor boundary label changed")
    return database, replay, labels


def build_plan() -> dict[str, object]:
    verify_release_and_predecessor()
    database, replay, labels = load_checked_closure()
    proof_hashes = {
        label: proof_ops_digest(database.statements[label]) for label in labels
    }
    chunks: list[dict[str, object]] = []
    previous_output: str | None = None
    previous_module = PREDECESSOR_MODULE
    for index, (chunk_id, start, end) in enumerate(CHUNK_SPECS):
        selected = labels[start - 1:end]
        first, last = EXPECTED_BOUNDARIES[chunk_id]
        require(selected[0] == first and selected[-1] == last,
                f"chunk {chunk_id} boundary labels changed")
        selected_proofs = {label: proof_hashes[label] for label in selected}
        lower = chunk_id.lower()
        module = f"NominalWPPReplayChunk{chunk_id}Compact001"
        output = f"reusable_nominal_mm_translator_v1_chunk{lower}_compact_001"
        predecessor = (
            {
                "kind": "kernel-trust-zero-exact-three",
                "resource": relative(PREDECESSOR_RESOURCE),
                "resourceSha256": PREDECESSOR_RESOURCE_SHA256,
                "module": PREDECESSOR_MODULE,
                "endTheoremOrdinal": PREDECESSOR_END_ORDINAL,
            }
            if index == 0
            else {
                "kind": "generated-source-only-chain",
                "resource": f"{previous_output}/resource.json",
                "resourceSha256": "COMPUTE_AND_VERIFY_AFTER_PREVIOUS_TRANSLATION",
                "module": previous_module,
                "endTheoremOrdinal": start - 1,
            }
        )
        chunks.append(
            {
                "chunkId": chunk_id,
                "startTheoremOrdinal": start,
                "endTheoremOrdinal": end,
                "theoremCount": end - start + 1,
                "firstLabel": first,
                "lastLabel": last,
                "selectedLabelsSha256": canonical_json_sha256(selected),
                "selectedProofOpsMapSha256": canonical_json_sha256(selected_proofs),
                "modulePrefix": module,
                "outputDirectory": output,
                "predecessor": predecessor,
            }
        )
        previous_output = output
        previous_module = module

    require(chunks[0]["startTheoremOrdinal"] == REMAINING_START,
            "remaining plan starts at the wrong ordinal")
    require(chunks[-1]["endTheoremOrdinal"] == REMAINING_END,
            "remaining plan ends at the wrong ordinal")
    for left, right in zip(chunks, chunks[1:]):
        require(left["endTheoremOrdinal"] + 1 == right["startTheoremOrdinal"],
                "remaining chunks are not contiguous")
    remaining_labels = labels[REMAINING_START - 1:REMAINING_END]
    remaining_proofs = {label: proof_hashes[label] for label in remaining_labels}
    return {
        "schema": "nf-wpp-remaining-replay-plan-v1",
        "status": "PASS_SOURCE_ONLY_DETERMINISTIC_PLAN_ALPHA97_KERNEL_PENDING",
        "planId": "NF_WPP_REMAINING_REPLAY_2867_4321_V1",
        "leanStartedByPlanner": False,
        "source": {
            "path": workspace_relative(SOURCE),
            "sha256": SOURCE_SHA256,
            "bytes": SOURCE_BYTES,
            "includesAbsent": True,
            "allMetamathProofsVerified": True,
        },
        "endpoint": {
            "label": ENDPOINT,
            "expression": list(ENDPOINT_EXPRESSION),
            "ast": replay["endpointAst"],
            "astWitness": relative(PREDECESSOR_SOURCE_AUDIT),
            "astWitnessSha256": PREDECESSOR_SOURCE_AUDIT_SHA256,
            "closureAssertionCount": replay["closureAssertionCount"],
            "closureProofTheoremCount": len(labels),
            "closureLabelsSha256": canonical_json_sha256(labels),
            "closureProofOpsMapSha256": canonical_json_sha256(proof_hashes),
            "endpointProofOpsSha256": proof_hashes[ENDPOINT],
        },
        "release": {
            "releaseId": "NF_WPP_TRANSLATOR_TOOLCHAIN_002",
            "manifest": relative(RELEASE_MANIFEST),
            "manifestSha256": RELEASE_MANIFEST_SHA256,
            "independentAudit": relative(RELEASE_AUDIT),
            "independentAuditSha256": RELEASE_AUDIT_SHA256,
            "translator": relative(TRANSLATOR),
            "translatorSha256": TRANSLATOR_SHA256,
            "profileId": "WPP_PROFILE_V2",
            "profile": relative(PROFILE),
            "profileSha256": PROFILE_SHA256,
        },
        "requiredAlphaFrontier": {
            "acceptanceState": "PENDING_EXTERNAL_KERNEL_RESOURCE",
            "resourcePathAndSha256MustBeSuppliedAtRuntime": True,
            "requiredStatusPrefix": "PASS_KERNEL_FIRST_USE_PREFIX_",
            "requiredTrust": 0,
            "requiredExactAllowedAxioms": [
                "propext", "Classical.choice", "Quot.sound"
            ],
            "requiredEndOrdinal": 97,
            "expectedOrdinal97SourceLabel": "df-wppgamma",
            "expectedOrdinal97SourceModule":
                "NominalAlphaCompactWpp001026WppgammaEnvFresh001",
            "currentSourceAuthorityPinnedAsFinal": False,
        },
        "acceptedPredecessor": {
            "resource": relative(PREDECESSOR_RESOURCE),
            "resourceSha256": PREDECESSOR_RESOURCE_SHA256,
            "sourceResourceSha256": PREDECESSOR_SOURCE_RESOURCE_SHA256,
            "module": PREDECESSOR_MODULE,
            "endTheoremOrdinal": PREDECESSOR_END_ORDINAL,
            "lastLabel": PREDECESSOR_LAST_LABEL,
            "boundaryKind": "kernel-trust-zero-exact-three",
        },
        "remainingInterval": {
            "startTheoremOrdinal": REMAINING_START,
            "endTheoremOrdinal": REMAINING_END,
            "theoremCount": len(remaining_labels),
            "firstLabel": remaining_labels[0],
            "lastLabel": remaining_labels[-1],
            "selectedLabelsSha256": canonical_json_sha256(remaining_labels),
            "selectedProofOpsMapSha256": canonical_json_sha256(remaining_proofs),
        },
        "partitionPolicy": {
            "logicalChunkWidth": 250,
            "logicalChunkOneStartOrdinal": 5,
            "chunk012SplitReason": "accepted alpha49 frontier ended at theorem 2866",
            "maximumCopiedTheoremBytesPerLeanPart": SPLIT_BYTES,
            "namespace": NAMESPACE,
            "chunkCount": len(chunks),
            "chunksContiguousAndComplete": True,
        },
        "chunks": chunks,
        "invocationPolicy": {
            "fullIntervalAlpha97AuditBeforeEmission": True,
            "firstChunkUsesAcceptedKernelPredecessor": True,
            "laterChunksUseHashVerifiedGeneratedSourcePredecessors": True,
            "outputDirectoriesAppendOnly": True,
            "translatorMustRecheckSourceClosureAndLeafCoverage": True,
            "leanInvocationForbidden": True,
        },
    }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check-existing", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    plan = build_plan()
    content = json_bytes(plan)
    output = args.output.resolve()
    require(output.parent.is_dir(), f"output parent does not exist: {output.parent}")
    if args.check_existing:
        require(output.is_file(), f"missing existing plan: {output}")
        require(output.read_bytes() == content, "existing plan differs byte-for-byte")
        print(f"PASS deterministic plan {sha256_bytes(content)}")
        return 0
    require(not output.exists(), f"refusing to overwrite plan: {output}")
    output.write_bytes(content)
    require(output.read_bytes() == content, "published plan differs")
    print(f"PASS wrote {output} sha256={sha256_bytes(content)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
