#!/usr/bin/env python3
"""Source-only successor audit for the whitespace-safe endpoint runner."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any


PREDECESSOR_RESOURCE_SHA256 = (
    "6B72CFD842C15A798155A3A440D0D7ABD9BBF72190D541806AC0724F0186BDD2"
)
PREDECESSOR_RUNNER_SHA256 = (
    "DB3C60251C597800ACB1A5783F7127740E698F1ADFA7C2BC26F615B7F3BCADCB"
)

OLD_PARSER = """function Assert-ExactPrints([string]$Stdout, [string[]]$Theorems) {
  $lines = @(($Stdout -split "`r?`n") | Where-Object { $_ -ne '' })
  if ($lines.Count -ne $Theorems.Count) {
    throw "Expected $($Theorems.Count) exact-three lines, found $($lines.Count)"
  }
  for ($i = 0; $i -lt $Theorems.Count; $i++) {
    $expected = "'$($Theorems[$i])' depends on axioms: [propext, Classical.choice, Quot.sound]"
    if ($lines[$i] -ne $expected) {
      throw "Exact-three print mismatch for $($Theorems[$i])"
    }
  }
}
"""

NEW_PARSER = r"""function Assert-ExactPrints([string]$Stdout, [string[]]$Theorems) {
  $pieces = @()
  foreach ($theorem in $Theorems) {
    $pieces += "'" + [regex]::Escape($theorem) +
      "'\s+depends\s+on\s+axioms\s*:\s*\[\s*propext\s*,\s*" +
      "Classical\.choice\s*,\s*Quot\.sound\s*\]"
  }
  $pattern = "\A\s*" + ($pieces -join "\s*") + "\s*\z"
  if (-not [regex]::IsMatch(
      $Stdout,
      $pattern,
      [Text.RegularExpressions.RegexOptions]::CultureInvariant
    )) {
    throw "Exact-three print mismatch for $($Theorems -join ', ')"
  }
}
"""


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def demand(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def file_record(path: Path) -> dict[str, Any]:
    return {
        "path": str(path.resolve()),
        "bytes": path.stat().st_size,
        "sha256": sha256(path),
    }


def resolve_recorded(value: str, anchor: Path) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = anchor.parent / path
    return path.resolve(strict=True)


def check_record(record: dict[str, Any], anchor: Path, context: str) -> Path:
    path = resolve_recorded(str(record["path"]), anchor)
    demand(path.stat().st_size == record["bytes"], f"byte count changed: {context}")
    demand(sha256(path) == str(record["sha256"]).upper(),
           f"SHA-256 changed: {context}")
    return path


def expected_successor(old_text: str) -> str:
    demand(old_text.count(OLD_PARSER) == 1, "predecessor parser block mismatch")
    text = old_text.replace(OLD_PARSER, NEW_PARSER)
    old_status = "PASS_SOURCE_ONLY_FINAL_ENDPOINT_PACKAGE_V1"
    demand(text.count(old_status) == 1, "predecessor package status count mismatch")
    text = text.replace(old_status, "PASS_SOURCE_ONLY_FINAL_ENDPOINT_PACKAGE_V2")
    old_schema = "nf-nominal-wpp-final-endpoint-kernel-v1"
    demand(text.count(old_schema) == 1, "predecessor kernel schema count mismatch")
    return text.replace(old_schema, "nf-nominal-wpp-final-endpoint-kernel-v2")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    base = Path(__file__).resolve().parent
    predecessor_path = base / "nominal_wpp_final_endpoint_package_source_audit_005/resource.json"
    old_runner = base / "run_nominal_wpp_final_endpoint_trust0_v1.ps1"
    new_runner = base / "run_nominal_wpp_final_endpoint_trust0_v2.ps1"
    demand(sha256(predecessor_path) == PREDECESSOR_RESOURCE_SHA256,
           "predecessor package resource hash mismatch")
    demand(sha256(old_runner) == PREDECESSOR_RUNNER_SHA256,
           "predecessor runner hash mismatch")
    predecessor = json.loads(predecessor_path.read_text(encoding="utf-8"))
    demand(predecessor["schema"] ==
           "nf-nominal-wpp-final-endpoint-package-source-audit-v1",
           "predecessor package schema mismatch")
    demand(predecessor["status"] == "PASS_SOURCE_ONLY_FINAL_ENDPOINT_PACKAGE_V1",
           "predecessor package status mismatch")
    demand(predecessor["leanStartedByThisAudit"] is False,
           "predecessor package unexpectedly started Lean")

    for name, record in predecessor["files"].items():
        check_record(record, predecessor_path, f"package file {name}")
    for row in predecessor["staticInputs"]:
        check_record(row, predecessor_path, f"static input {row['name']}")
    for row in predecessor["supportOleans"]:
        check_record(row, predecessor_path, f"support olean {row['module']}")

    old_text = old_runner.read_text(encoding="utf-8-sig")
    new_text = new_runner.read_text(encoding="utf-8-sig")
    demand(new_text == expected_successor(old_text),
           "runner v2 is not the exact audited three-change successor")
    demand("\\A\\s*" in new_text and "\\s*\\z" in new_text,
           "runner v2 lacks whole-output anchors")
    demand("[regex]::Escape($theorem)" in new_text,
           "runner v2 does not escape theorem names")
    demand("Classical\\.choice" in new_text and "Quot\\.sound" in new_text,
           "runner v2 exact-three pattern changed")

    resource = copy.deepcopy(predecessor)
    resource["schema"] = "nf-nominal-wpp-final-endpoint-package-source-audit-v2"
    resource["status"] = "PASS_SOURCE_ONLY_FINAL_ENDPOINT_PACKAGE_V2"
    resource["predecessorPackageAudit"] = {
        "path": str(predecessor_path.resolve()),
        "sha256": PREDECESSOR_RESOURCE_SHA256,
    }
    resource["files"]["predecessorRunner"] = file_record(old_runner)
    resource["files"]["runner"] = file_record(new_runner)
    resource["files"]["auditor"] = file_record(Path(__file__))
    resource["sourceOnlyChecks"]["whitespaceTolerantExactThreeParser"] = "PASS"
    resource["sourceOnlyChecks"]["exactRunnerSuccessorDelta"] = "PASS"
    resource["sourceOnlyChecks"]["leanProcessesStarted"] = 0

    output = args.output.resolve()
    demand(not output.exists(), f"refusing to overwrite audit resource: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(resource, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({
        "status": resource["status"],
        "resource": str(output),
        "resourceSha256": sha256(output),
        "runnerSha256": sha256(new_runner),
        "leanStarted": False,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
