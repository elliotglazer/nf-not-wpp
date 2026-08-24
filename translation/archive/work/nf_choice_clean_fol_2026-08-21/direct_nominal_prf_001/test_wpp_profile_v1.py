#!/usr/bin/env python3
"""Focused fail-closed tests for the reusable translator's WPP profile.

The tests hash files and import Python backends only.  They never invoke Lean
or emit a Metamath replay closure.
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


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import reusable_nominal_mm_translator_v1 as cli


@contextmanager
def test_directory():  # type: ignore[no-untyped-def]
    root = HERE / f".wpp-profile-test-{uuid.uuid4().hex}"
    root.mkdir(parents=False, exist_ok=False)
    try:
        yield root
    finally:
        shutil.rmtree(root)


def manifest_data() -> dict[str, object]:
    return json.loads(cli.WPP_PROFILE_V1_MANIFEST.read_text(encoding="utf-8"))


def write_manifest(path: Path, data: object) -> str:
    path.write_bytes(cli.json_bytes(data))
    return cli.sha256(path)


class WPPProfileV1Tests(unittest.TestCase):
    def test_01_real_profile_has_exact_bounded_census(self) -> None:
        profile = cli.load_wpp_profile_v1()
        self.assertEqual(profile["profileId"], "WPP_PROFILE_V1")
        self.assertEqual(profile["inputCount"], 92)
        self.assertEqual(profile["pythonModuleCount"], 19)
        self.assertEqual(profile["fixedDataCount"], 73)
        self.assertEqual(
            len(profile["orderedInputSets"]["choiceAlphaCallManifests"]), 64
        )
        paths = list(profile["_resolvedInputs"].values())
        self.assertEqual(len(paths), len(set(paths)))
        self.assertTrue(all(path.is_file() for path in paths))
        provenance = cli.wpp_profile_provenance(profile)
        self.assertEqual(
            provenance["manifestSha256"], cli.WPP_PROFILE_V1_MANIFEST_SHA256
        )
        self.assertTrue(provenance["staticInputsVerifiedBeforeBackendImport"])
        self.assertTrue(provenance["backendImportsForcedFromVerifiedSource"])

    def test_10_manifest_bytes_are_pinned_before_json_use(self) -> None:
        with test_directory() as root:
            tampered = root / "tampered-profile.json"
            tampered.write_bytes(cli.WPP_PROFILE_V1_MANIFEST.read_bytes() + b"\n")
            with self.assertRaisesRegex(RuntimeError, "manifest SHA-256 mismatch"):
                cli.verify_wpp_profile_manifest(
                    tampered, cli.WPP_PROFILE_V1_MANIFEST_SHA256
                )

    def test_20_static_input_hash_tamper_fails_closed(self) -> None:
        with test_directory() as root:
            data = copy.deepcopy(manifest_data())
            data["inputs"][0]["sha256"] = "A" * 64
            path = root / "wrong-input-hash.json"
            pin = write_manifest(path, data)
            with self.assertRaisesRegex(RuntimeError, "profile input.*SHA-256 mismatch"):
                cli.verify_wpp_profile_manifest(path, pin)

    def test_30_input_set_digest_tamper_fails_closed(self) -> None:
        with test_directory() as root:
            data = copy.deepcopy(manifest_data())
            data["inputSetSha256"] = "B" * 64
            path = root / "wrong-input-set.json"
            pin = write_manifest(path, data)
            with self.assertRaisesRegex(RuntimeError, "input-set digest changed"):
                cli.verify_wpp_profile_manifest(path, pin)

    def test_40_path_escape_fails_before_file_read(self) -> None:
        with test_directory() as root:
            data = copy.deepcopy(manifest_data())
            data["inputs"][0]["path"] = "../outside.py"
            path = root / "escaping-input.json"
            pin = write_manifest(path, data)
            with self.assertRaisesRegex(RuntimeError, "escaping path"):
                cli.verify_wpp_profile_manifest(path, pin)

    def test_50_duplicate_static_path_fails_closed(self) -> None:
        with test_directory() as root:
            data = copy.deepcopy(manifest_data())
            data["inputs"][1]["path"] = data["inputs"][0]["path"]
            path = root / "duplicate-input.json"
            pin = write_manifest(path, data)
            with self.assertRaisesRegex(RuntimeError, "duplicate WPP profile input path"):
                cli.verify_wpp_profile_manifest(path, pin)

    def test_60_preloaded_backend_module_is_rejected(self) -> None:
        sentinel = object()
        prior = sys.modules.get("mm_parser", sentinel)
        sys.modules["mm_parser"] = type("Injected", (), {})()
        try:
            with self.assertRaisesRegex(RuntimeError, "preloaded before verification"):
                cli.prepare_verified_profile_imports(cli.load_wpp_profile_v1())
        finally:
            if prior is sentinel:
                del sys.modules["mm_parser"]
            else:
                sys.modules["mm_parser"] = prior

    def test_90_fresh_backend_uses_absent_verified_source_cache(self) -> None:
        script = (
            "import json,sys; from pathlib import Path; "
            f"h=Path({str(HERE)!r}); sys.path.insert(0,str(h)); "
            "import reusable_nominal_mm_translator_v1 as c; "
            "p=c.load_wpp_profile_v1(); b=c.load_backend(); "
            "mods=[r['module'] for r in p['inputs'] "
            "if r['kind']=='python-module-source' and "
            "r['module']!='nominal_alpha_dispatch_core_v1_pinned']; "
            "cached=[getattr(sys.modules[n],'__cached__',None) for n in mods]; "
            "print(json.dumps({'prefix':sys.pycache_prefix,"
            "'prefixExists':Path(sys.pycache_prefix).exists(),"
            "'allCachedUnderPrefix':all(x and str(x).startswith(sys.pycache_prefix) "
            "for x in cached),'alphaCount':len(b.wpp_base.choice_replay.ALPHA_CALL_MANIFESTS)}))"
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
        self.assertFalse(report["prefixExists"])
        self.assertTrue(report["allCachedUnderPrefix"])
        self.assertEqual(report["alphaCount"], 64)


if __name__ == "__main__":
    unittest.main(verbosity=2)
