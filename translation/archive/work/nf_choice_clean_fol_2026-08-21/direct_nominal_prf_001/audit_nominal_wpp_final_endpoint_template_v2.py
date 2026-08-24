#!/usr/bin/env python3
"""Source-only audit for the one-line final endpoint template repair.

The accepted runner contract remains V2.  This audit proves that the package
differs from its accepted predecessor only by joining one qualified Lean name
which Lean cannot parse across a trailing-dot newline.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
from pathlib import Path
from typing import Any


PREDECESSOR_RESOURCE_SHA256 = (
    "E711D4726D51C61D8C964368B7B746227EFE35AFFE65EE8CEC5C9847C085115D"
)
RUNNER_SHA256 = (
    "6A523BFFFE87BCFF5C7C39116CC3F44A9DF70B6AF8B39C1207E9B44A4D8E1FDC"
)
OLD_TEMPLATE_SHA256 = (
    "9E5DFF84CCE299D47F03ABFB9A284B9BB6288E2C728F8AF71549CF3FDDFE8B08"
)
NEW_TEMPLATE_SHA256 = (
    "096B2BC67B9560CAD143C6DE84C202818DCA285DAFDAED75E2BF1AB69F34FECA"
)

OLD_FRAGMENT = """  exact
    NFChoice.DirectNominalPrf.Nominal.ClosedEndpointBridgeV1.
      hailperinNF_derives_not_WPP_of_nominal generatedEndpoint
"""

NEW_FRAGMENT = """  exact
    NFChoice.DirectNominalPrf.Nominal.ClosedEndpointBridgeV1.hailperinNF_derives_not_WPP_of_nominal
      generatedEndpoint
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
    demand(path.stat().st_size == record["bytes"],
           f"byte count changed: {context}")
    demand(sha256(path) == str(record["sha256"]).upper(),
           f"SHA-256 changed: {context}")
    return path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    base = Path(__file__).resolve().parent
    predecessor_path = (
        base / "nominal_wpp_final_endpoint_package_source_audit_006/resource.json"
    )
    old_template = base / "NOMINAL_WPP_FINAL_ENDPOINT_V1.lean.in"
    new_template = base / "NOMINAL_WPP_FINAL_ENDPOINT_V2.lean.in"
    runner = base / "run_nominal_wpp_final_endpoint_trust0_v2.ps1"

    demand(sha256(predecessor_path) == PREDECESSOR_RESOURCE_SHA256,
           "predecessor package resource hash mismatch")
    demand(sha256(old_template) == OLD_TEMPLATE_SHA256,
           "predecessor template hash mismatch")
    demand(sha256(new_template) == NEW_TEMPLATE_SHA256,
           "successor template hash mismatch")
    demand(sha256(runner) == RUNNER_SHA256, "runner v2 hash mismatch")

    predecessor = json.loads(predecessor_path.read_text(encoding="utf-8"))
    demand(predecessor["schema"] ==
           "nf-nominal-wpp-final-endpoint-package-source-audit-v2",
           "predecessor package schema mismatch")
    demand(predecessor["status"] ==
           "PASS_SOURCE_ONLY_FINAL_ENDPOINT_PACKAGE_V2",
           "predecessor package status mismatch")
    demand(predecessor["leanStartedByThisAudit"] is False,
           "predecessor package unexpectedly started Lean")

    for name, record in predecessor["files"].items():
        check_record(record, predecessor_path, f"package file {name}")
    for row in predecessor["staticInputs"]:
        check_record(row, predecessor_path, f"static input {row['name']}")
    for row in predecessor["supportOleans"]:
        check_record(row, predecessor_path, f"support olean {row['module']}")

    old_text = old_template.read_text(encoding="utf-8")
    new_text = new_template.read_text(encoding="utf-8")
    demand(old_text.count(OLD_FRAGMENT) == 1,
           "predecessor split-name fragment count mismatch")
    demand(new_text == old_text.replace(OLD_FRAGMENT, NEW_FRAGMENT),
           "template V2 is not the exact one-fragment successor")
    demand("ClosedEndpointBridgeV1.\n" not in new_text,
           "successor template still splits a name after the dot")
    demand(new_text.count("@@FINAL_REPLAY_MODULE@@") == 1,
           "successor template placeholder count changed")
    demand(re.search(r"(?m)^\s*(axiom|opaque)\b|\bsorry\b", new_text) is None,
           "successor template contains a forbidden declaration or placeholder")

    runner_text = runner.read_text(encoding="utf-8-sig")
    demand("PASS_SOURCE_ONLY_FINAL_ENDPOINT_PACKAGE_V2" in runner_text,
           "runner no longer accepts the audited package contract")
    demand("'--template', $template" in runner_text,
           "runner does not pass the package-recorded template")
    demand("\\A\\s*" in runner_text and "\\s*\\z" in runner_text,
           "runner lost its whole-output exact-three anchors")

    resource = copy.deepcopy(predecessor)
    prior_lineage = resource.get("predecessorPackageAudit")
    resource["schema"] = (
        "nf-nominal-wpp-final-endpoint-package-source-audit-v2-template2"
    )
    resource["status"] = "PASS_SOURCE_ONLY_FINAL_ENDPOINT_PACKAGE_V2"
    resource["predecessorPackageAudit"] = {
        "path": str(predecessor_path.resolve()),
        "sha256": PREDECESSOR_RESOURCE_SHA256,
    }
    resource["earlierPackageAudit"] = prior_lineage
    resource["files"]["predecessorTemplate"] = file_record(old_template)
    resource["files"]["predecessorAuditor"] = resource["files"]["auditor"]
    resource["files"]["template"] = file_record(new_template)
    resource["files"]["runner"] = file_record(runner)
    resource["files"]["auditor"] = file_record(Path(__file__))
    resource["sourceOnlyChecks"]["exactTemplateSuccessorDelta"] = "PASS"
    resource["sourceOnlyChecks"]["qualifiedIdentifierContiguous"] = "PASS"
    resource["sourceOnlyChecks"]["runnerContractUnchanged"] = "PASS"
    resource["sourceOnlyChecks"]["leanProcessesStarted"] = 0

    output = args.output.resolve()
    demand(not output.exists(), f"refusing to overwrite audit resource: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(resource, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps({
        "status": resource["status"],
        "schema": resource["schema"],
        "resource": str(output),
        "resourceSha256": sha256(output),
        "templateSha256": sha256(new_template),
        "runnerSha256": sha256(runner),
        "leanStarted": False,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
