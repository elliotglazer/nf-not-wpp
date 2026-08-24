#!/usr/bin/env python3
"""Independent source/provenance audit of NF/WPP translator Release004."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import uuid


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "translator_release_nf_wpp_004" / "manifest.json"
MANIFEST_SHA256 = "B8B1128D2AAFC5882BC7AB72B2EE0C821CE1CB76C96D6A4C9E8223AC56BEFE98"
OUT = HERE / "translator_release_nf_wpp_004_audit_001"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def digest_text(value: str) -> str:
    return digest(value.encode("utf-8"))


def check(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def resolve(value: str) -> Path:
    path = Path(value)
    return (HERE / path).resolve() if not path.is_absolute() else path.resolve()


def pin(path: Path, expected: str, description: str) -> None:
    check(path.is_file() and digest(path.read_bytes()) == expected,
          f"{description} changed: {path}")


def main() -> None:
    check(not OUT.exists(), f"refusing to overwrite append-only audit: {OUT}")
    pin(MANIFEST, MANIFEST_SHA256, "Release004 manifest")
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    check(manifest.get("schema") == "nf-reusable-nominal-mm-translator-release-v4"
          and manifest.get("status") ==
              "PASS_SOURCE_ONLY_NATIVE_BARE_DUMMY_FINE_V7_COARSE_V8_KERNEL_VERIFICATION_SEPARATE"
          and manifest.get("leanStartedByThisReleasePackaging") is False,
          "Release004 manifest contract changed")

    pins = []
    def verify(value: str, expected: str, description: str) -> Path:
        path = resolve(value)
        pin(path, expected, description)
        pins.append(f"{description}|{path}|{expected}|{path.stat().st_size}")
        return path

    supersedes = manifest["supersedes"]
    verify(supersedes["manifest"], supersedes["manifestSha256"],
           "Release003 manifest")
    verify(supersedes["independentAudit"], supersedes["independentAuditSha256"],
           "Release003 independent audit")
    benchmark = manifest["benchmarkGate"]
    verify(benchmark["part004Resource"], benchmark["part004ResourceSha256"],
           "B51 Part004 trust0 resource")
    verify(benchmark["part025Resource"], benchmark["part025ResourceSha256"],
           "B51 Part025 trust0 resource")

    native = manifest["nativeStructuralBackend"]
    verify(native["path"], native["sha256"], "Release004 backend")
    verify(native["parent"], native["parentSha256"], "Release003 backend parent")
    for index, row in enumerate(native["nativeResources"]):
        verify(row["path"], row["sha256"], f"native resource {index}")
    for index, row in enumerate(native["nativeProducers"]):
        verify(row["path"], row["sha256"], f"native producer {index}")
    for index, row in enumerate(native["audits"]):
        verify(row["path"], row["sha256"], f"native audit {index}")
    check(native["suffixCandidateCount"] == 19_227
          and native["suffixExactAliasCount"] == 38
          and native["global51Through97CandidateCount"] == 19_335
          and native["global51Through97ExactAliasCount"] == 41
          and native["allNativeInverseByteIdentical"] is True,
          "Release004 native census changed")

    fine = manifest["fineLiftV7"]
    verify(fine["lifter"], fine["lifterSha256"], "fine V7 lifter")
    verify(fine["authority"], fine["authoritySha256"], "Release004 lift authority")
    verify(fine["b51Manifest"], fine["b51ManifestSha256"], "fine V7 B51 manifest")
    verify(fine["b51InverseAudit"], fine["b51InverseAuditSha256"],
           "fine V7 B51 inverse")
    fine_index_path = verify(fine["suffixIndex"], fine["suffixIndexSha256"],
                             "fine V7 suffix index")
    fine_index = json.loads(fine_index_path.read_text(encoding="utf-8"))
    check(fine_index["totals"] == {
        "recordCount": 46,
        "declarationCount": 59_794,
        "proofDataDefinitionCount": 3_673,
        "moduleCount": 5_147,
        "largeSingletonCount": 0,
        "nativeBareDummySimpCount": 19_227,
        "exactAliasExclusionCount": 38,
    }, "fine V7 suffix totals changed")
    check(fine["declarationCount"] == 60_117
          and fine["proofDataDefinitionCount"] == 3_688
          and fine["nativeBareDummySimpCount"] == 19_335
          and fine["moduleCount"] == 5_176
          and fine["appliedDummyInsideSimpListCount"] == 0,
          "fine V7 unified totals changed")

    coarse = manifest["coarseLiftV8"]
    verify(coarse["lifter"], coarse["lifterSha256"], "coarse V8 lifter")
    coarse_index_path = verify(coarse["index"], coarse["indexSha256"],
                               "coarse V8 index")
    coarse_audit_path = verify(coarse["independentAudit"],
                               coarse["independentAuditSha256"],
                               "coarse V8 independent audit")
    coarse_index = json.loads(coarse_index_path.read_text(encoding="utf-8"))
    coarse_audit = json.loads(coarse_audit_path.read_text(encoding="utf-8"))
    expected_totals = {
        "recordCount": 47,
        "declarationCount": 60_117,
        "proofDataDefinitionCount": 3_688,
        "nativeBareDummySimpCount": 19_335,
        "exactAliasExclusionCount": 41,
        "fineModuleCount": 5_176,
        "coarseModuleCount": 910,
        "largeSingletonCount": 0,
    }
    check(all(coarse_index["totals"].get(key) == value
              and coarse_audit["totals"].get(key) == value
              for key, value in expected_totals.items()),
          "coarse V8 index/audit totals changed")
    check(coarse_audit["declarationLedgerSha256"] ==
          coarse["declarationLedgerSha256"]
          and coarse_audit["partitionLedgerSha256"] ==
              coarse["partitionLedgerSha256"]
          and coarse_audit["allExactInverse"] is True,
          "coarse V8 independent ledgers changed")

    tests = manifest["tests"]
    test_path = verify(tests["results"], tests["resultsSha256"],
                       "Release004 source tests")
    test_data = json.loads(test_path.read_text(encoding="utf-8"))
    check(test_data["status"] == "PASS_SOURCE_ONLY_NO_LEAN"
          and test_data["suiteCount"] == 9
          and test_data["testCount"] == 76
          and test_data["leanStarted"] is False,
          "Release004 source test contract changed")
    verify(manifest["design"]["path"], manifest["design"]["sha256"],
           "Release004 design")
    for index, row in enumerate(manifest["artifacts"]):
        path = verify(row["path"], row["sha256"], f"manifest artifact {index}")
        check(path.stat().st_size == int(row["bytes"]),
              f"manifest artifact size changed: {path}")

    check(manifest["scope"]["statementsApplicationsSubstitutionsDependenciesChanged"]
          is False
          and manifest["scope"]["acceptedRelease003ArtifactsMutated"] is False
          and manifest["scope"]["fullEndpointClaimedByThisRelease"] is False,
          "Release004 scope/trust statement changed")
    stage = HERE / f".{OUT.name}.stage-{uuid.uuid4().hex[:10]}"
    stage.mkdir()
    resource = {
        "schema": "nf-reusable-nominal-mm-translator-release-v4-independent-audit",
        "status": "PASS_RELEASE004_SOURCE_PROVENANCE_EXACT_KERNEL_VERIFICATION_SEPARATE",
        "createdUtc": datetime.now(timezone.utc).isoformat(),
        "leanInvoked": False,
        "producer": str(Path(__file__).resolve()),
        "producerSha256": digest(Path(__file__).read_bytes()),
        "releaseManifest": str(MANIFEST.resolve()),
        "releaseManifestSha256": MANIFEST_SHA256,
        "verifiedPinCount": len(pins),
        "verifiedPinLedgerSha256": digest_text("\n".join(pins) + "\n"),
        "globalRange": {"first": 51, "last": 97, "count": 47},
        "nativeBareDummySimpCount": 19_335,
        "exactAliasExclusionCount": 41,
        "declarationCount": 60_117,
        "proofDataDefinitionCount": 3_688,
        "fineModuleCount": 5_176,
        "coarseModuleCount": 910,
        "declarationLedgerSha256": coarse["declarationLedgerSha256"],
        "partitionLedgerSha256": coarse["partitionLedgerSha256"],
        "allNativeInverseByteIdentical": True,
        "allFineToCoarseDeclarationRowsIdentical": True,
        "allLiftInverseExact": True,
        "allPublicStatementsAndSignaturesByteIdentical": True,
        "allProofDataKeywordsPreserved": True,
        "appliedDummyInsideSimpListCount": 0,
        "genericProofSearch": False,
        "opaqueDeclarations": False,
        "fullEndpointClaimed": False,
        "mismatches": [],
    }
    target = stage / "resource.json"
    target.write_text(json.dumps(resource, indent=2) + "\n",
                      encoding="utf-8", newline="\n")
    stage.replace(OUT)
    final = OUT / "resource.json"
    print(json.dumps({
        "status": resource["status"],
        "resource": str(final),
        "resourceSha256": digest(final.read_bytes()),
        "verifiedPinCount": len(pins),
        "verifiedPinLedgerSha256": resource["verifiedPinLedgerSha256"],
    }, indent=2))


if __name__ == "__main__":
    main()
