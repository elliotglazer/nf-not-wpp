#!/usr/bin/env python3
"""Focused source-only tests for immutable ``WPP_PROFILE_V2``.

The suite exercises manifest lineage, global72/a4972 semantic joins, profile
selection, verified-source imports, and tamper failure.  It never invokes Lean
or emits a replay closure.
"""

from __future__ import annotations

from contextlib import contextmanager
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import unittest
import uuid
from typing import Any, Iterator


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import reusable_nominal_mm_translator_v1 as cli


@contextmanager
def test_directory() -> Iterator[Path]:
    root = HERE / f".wpp-profile-v2-test-{uuid.uuid4().hex}"
    root.mkdir(parents=False, exist_ok=False)
    try:
        yield root
    finally:
        shutil.rmtree(root)


def manifest_data() -> dict[str, Any]:
    value = json.loads(cli.WPP_PROFILE_V2_MANIFEST.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError("V2 manifest is not an object")
    return value


def write_json(path: Path, value: object) -> str:
    path.write_bytes(cli.json_bytes(value))
    return cli.sha256(path)


def recalculate_input_set(data: dict[str, Any]) -> None:
    data["inputSetSha256"] = cli.canonical_json_sha256(
        [
            {
                key: entry[key]
                for key in ("id", "root", "path", "kind", "bytes", "sha256")
            }
            for entry in data["inputs"]
        ]
    )


def replace_input_with_file(
    data: dict[str, Any], identifier: str, path: Path
) -> None:
    entry = next(row for row in data["inputs"] if row["id"] == identifier)
    entry["path"] = path.resolve().relative_to(WORKSPACE).as_posix()
    entry["bytes"] = path.stat().st_size
    entry["sha256"] = cli.sha256(path)
    recalculate_input_set(data)


class WPPProfileV2Tests(unittest.TestCase):
    def test_01_real_v2_is_exact_append_only_extension(self) -> None:
        v1 = cli.load_wpp_profile_v1()
        v2 = cli.load_wpp_profile_v2()
        self.assertEqual(v2["profileId"], "WPP_PROFILE_V2")
        self.assertEqual(v2["inputCount"], 97)
        self.assertEqual(v2["pythonModuleCount"], 20)
        self.assertEqual(v2["fixedDataCount"], 77)
        self.assertEqual(v2["inputs"][:92], v1["inputs"])
        self.assertEqual(
            v2["contracts"]["globalAlphaPrefix72"],
            cli.GLOBAL_PREFIX72_CONTRACT,
        )
        self.assertEqual(
            v2["contracts"]["a4972SourceMetadata"]["w1"]["label"],
            "df-iso",
        )
        provenance = cli.wpp_profile_provenance(v2)
        self.assertEqual(provenance["profileId"], "WPP_PROFILE_V2")
        self.assertEqual(
            provenance["manifestSha256"], cli.WPP_PROFILE_V2_MANIFEST_SHA256
        )

    def test_10_cli_default_is_v2_and_v1_remains_selectable(self) -> None:
        parser = cli.make_parser()
        profile_action = next(
            action for action in parser._actions
            if "--wpp-profile" in action.option_strings
        )
        self.assertEqual(profile_action.default, "WPP_PROFILE_V2")
        self.assertEqual(tuple(profile_action.choices), cli.WPP_PROFILE_IDS)
        option_names = {
            option
            for action in parser._actions
            for option in action.option_strings
        }
        legacy_required = {
            "--source", "--source-sha256", "--endpoint",
            "--alpha-frontier-resource", "--alpha-frontier-sha256",
            "--output-dir", "--split-bytes",
        }
        self.assertTrue(legacy_required.issubset(option_names))
        self.assertEqual(
            cli.load_wpp_profile("WPP_PROFILE_V1")["profileId"],
            "WPP_PROFILE_V1",
        )

    def test_20_manifest_bytes_are_pinned_before_parse(self) -> None:
        with test_directory() as root:
            path = root / "tampered-manifest.json"
            path.write_bytes(cli.WPP_PROFILE_V2_MANIFEST.read_bytes() + b"\n")
            with self.assertRaisesRegex(RuntimeError, "manifest SHA-256 mismatch"):
                cli.verify_wpp_profile_manifest(
                    path,
                    cli.WPP_PROFILE_V2_MANIFEST_SHA256,
                    profile_id="WPP_PROFILE_V2",
                )

    def test_30_static_input_hash_tamper_fails_closed(self) -> None:
        with test_directory() as root:
            data = copy.deepcopy(manifest_data())
            data["inputs"][-1]["sha256"] = "A" * 64
            path = root / "wrong-input-hash.json"
            pin = write_json(path, data)
            with self.assertRaisesRegex(RuntimeError, "profile input.*SHA-256 mismatch"):
                cli.verify_wpp_profile_manifest(
                    path, pin, profile_id="WPP_PROFILE_V2"
                )

    def test_40_inherited_v1_entry_mutation_fails_closed(self) -> None:
        with test_directory() as root:
            data = copy.deepcopy(manifest_data())
            data["inputs"][0]["readBy"] = ["tampered semantic role"]
            path = root / "wrong-parent-extension.json"
            pin = write_json(path, data)
            with self.assertRaisesRegex(RuntimeError, "inherit V1 entries"):
                cli.verify_wpp_profile_manifest(
                    path, pin, profile_id="WPP_PROFILE_V2"
                )

    def test_50_global72_contract_mutation_fails_closed(self) -> None:
        with test_directory() as root:
            data = copy.deepcopy(manifest_data())
            data["contracts"]["globalAlphaPrefix72"]["lastRecord"]["label"] = (
                "tampered"
            )
            path = root / "wrong-global-contract.json"
            pin = write_json(path, data)
            with self.assertRaisesRegex(RuntimeError, "global-alpha semantic contract"):
                cli.verify_wpp_profile_manifest(
                    path, pin, profile_id="WPP_PROFILE_V2"
                )

    def test_60_a4972_source_metadata_tamper_fails_closed(self) -> None:
        with test_directory() as root:
            data = copy.deepcopy(manifest_data())
            source = json.loads(
                data_path(data, "data:a4972-global-prefix72-source-manifest")
                .read_text(encoding="utf-8")
            )
            source["globalRecordContract"]["lastRecord"]["label"] = "tampered"
            tampered = root / "tampered-a4972-source.json"
            write_json(tampered, source)
            replace_input_with_file(
                data, "data:a4972-global-prefix72-source-manifest", tampered
            )
            path = root / "profile-with-tampered-a4972.json"
            pin = write_json(path, data)
            with self.assertRaisesRegex(RuntimeError, "a4972 metadata/input identity"):
                cli.verify_wpp_profile_manifest(
                    path, pin, profile_id="WPP_PROFILE_V2"
                )

    def test_70_independent_w1_join_tamper_fails_closed(self) -> None:
        with test_directory() as root:
            data = copy.deepcopy(manifest_data())
            join = json.loads(
                data_path(
                    data,
                    "data:a4972-global-prefix72-independent-join-audit",
                ).read_text(encoding="utf-8")
            )
            join["successor"]["w1Identity"]["originalSourceByteIdentical"] = False
            tampered = root / "tampered-a4972-join.json"
            write_json(tampered, join)
            replace_input_with_file(
                data,
                "data:a4972-global-prefix72-independent-join-audit",
                tampered,
            )
            path = root / "profile-with-tampered-join.json"
            pin = write_json(path, data)
            with self.assertRaisesRegex(RuntimeError, "a4972 metadata/input identity"):
                cli.verify_wpp_profile_manifest(
                    path, pin, profile_id="WPP_PROFILE_V2"
                )

    def test_90_fresh_v2_backend_is_verified_core_v3(self) -> None:
        script = (
            "import json,sys; from pathlib import Path; "
            f"h=Path({str(HERE)!r}); sys.path.insert(0,str(h)); "
            "import reusable_nominal_mm_translator_v1 as c; "
            "p=c.load_wpp_profile_v2(); b=c.load_backend('WPP_PROFILE_V2'); "
            "print(json.dumps({'profile':p['profileId'],"
            "'alphaModule':b.alpha_core.__name__,"
            "'globalCount':len(b.alpha_core.GLOBAL_RECORDS),"
            "'ordinal72':b.alpha_core.GLOBAL_RECORDS[71]['label'],"
            "'prefixExists':Path(sys.pycache_prefix).exists(),"
            "'contract':b.alpha_core.global_record_contract(72)}))"
        )
        run = subprocess.run(
            [sys.executable, "-B", "-c", script],
            cwd=WORKSPACE,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(run.returncode, 0, run.stderr)
        report = json.loads(run.stdout)
        self.assertEqual(report["profile"], "WPP_PROFILE_V2")
        self.assertEqual(report["alphaModule"], "nominal_alpha_dispatch_core_v3")
        self.assertEqual(report["globalCount"], 97)
        self.assertEqual(report["ordinal72"], "df-iso")
        self.assertFalse(report["prefixExists"])
        self.assertEqual(report["contract"], cli.GLOBAL_PREFIX72_CONTRACT)


def data_path(data: dict[str, Any], identifier: str) -> Path:
    entry = next(row for row in data["inputs"] if row["id"] == identifier)
    return WORKSPACE.joinpath(*Path(entry["path"]).parts).resolve()


if __name__ == "__main__":
    unittest.main(verbosity=2)
