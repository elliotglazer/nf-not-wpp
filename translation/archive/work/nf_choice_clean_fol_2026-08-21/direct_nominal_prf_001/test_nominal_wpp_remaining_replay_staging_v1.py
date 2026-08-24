#!/usr/bin/env python3
"""Source-only regressions for the post-alpha97 theorem replay staging."""

from __future__ import annotations

import json
from pathlib import Path
import unittest

import build_nominal_wpp_remaining_replay_plan_v1 as planner
import run_nominal_wpp_remaining_replay_translation_v1 as runner


HERE = Path(__file__).resolve().parent


class RemainingReplayStagingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.plan = planner.build_plan()

    def test_frozen_plan_is_exact_rebuild(self) -> None:
        self.assertEqual(runner.sha256(runner.PLAN), runner.PLAN_SHA256)
        self.assertEqual(
            runner.PLAN.read_bytes(), planner.json_bytes(self.plan)
        )

    def test_exact_remaining_interval(self) -> None:
        interval = self.plan["remainingInterval"]
        self.assertEqual(interval["startTheoremOrdinal"], 2867)
        self.assertEqual(interval["endTheoremOrdinal"], 4321)
        self.assertEqual(interval["theoremCount"], 1455)
        self.assertEqual(interval["firstLabel"], "isoeq1")
        self.assertEqual(interval["lastLabel"], planner.ENDPOINT)

    def test_seven_legacy_chunks_are_contiguous(self) -> None:
        chunks = self.plan["chunks"]
        self.assertEqual(len(chunks), 7)
        self.assertEqual(sum(row["theoremCount"] for row in chunks), 1455)
        self.assertEqual(chunks[0]["chunkId"], "012B")
        self.assertEqual(chunks[-1]["chunkId"], "018")
        for left, right in zip(chunks, chunks[1:]):
            self.assertEqual(
                left["endTheoremOrdinal"] + 1,
                right["startTheoremOrdinal"],
            )

    def test_chunk_modules_and_outputs_are_unique(self) -> None:
        chunks = self.plan["chunks"]
        self.assertEqual(
            len({row["modulePrefix"] for row in chunks}), len(chunks)
        )
        self.assertEqual(
            len({row["outputDirectory"] for row in chunks}), len(chunks)
        )

    def test_first_predecessor_is_accepted_chunk012a(self) -> None:
        predecessor = self.plan["chunks"][0]["predecessor"]
        self.assertEqual(predecessor["kind"], "kernel-trust-zero-exact-three")
        self.assertEqual(
            predecessor["resourceSha256"],
            planner.PREDECESSOR_RESOURCE_SHA256,
        )
        self.assertEqual(predecessor["endTheoremOrdinal"], 2866)

    def test_current_alpha49_is_rejected_as_not_alpha97(self) -> None:
        resource = HERE / "a49op1r1" / "resource.json"
        digest = runner.sha256(resource)
        with self.assertRaisesRegex(RuntimeError, "does not end at exact global ordinal 97"):
            runner.load_alpha97_resource(resource, digest)

    def test_false_trust_is_rejected_even_though_bool_equals_zero(self) -> None:
        source = json.loads(
            (HERE / "a49op1r1" / "resource.json").read_text(encoding="utf-8")
        )
        source["firstUsePrefix"]["endOrdinal"] = 97
        source["trust"] = False
        with self.assertRaisesRegex(RuntimeError, "trust level zero"):
            runner.validate_alpha97_data(source)

    def test_translation_command_is_source_translator_only(self) -> None:
        command = runner.translator_base(
            Path("alpha97.json").resolve(),
            "A" * 64,
            Path("out").resolve(),
            2867,
            3004,
            planner.PREDECESSOR_RESOURCE,
            planner.PREDECESSOR_RESOURCE_SHA256,
            "NominalWPPReplayChunk012BCompact001",
        )
        self.assertEqual(Path(command[1]).resolve(), planner.TRANSLATOR.resolve())
        self.assertNotIn("--trust", command)
        self.assertFalse(
            any(Path(argument).name.lower() == "lean.exe" for argument in command)
        )
        self.assertIn("--wpp-profile", command)
        self.assertIn("WPP_PROFILE_V2", command)

    def test_required_alpha97_state_remains_pending(self) -> None:
        alpha = self.plan["requiredAlphaFrontier"]
        self.assertEqual(alpha["acceptanceState"], "PENDING_EXTERNAL_KERNEL_RESOURCE")
        self.assertTrue(alpha["resourcePathAndSha256MustBeSuppliedAtRuntime"])
        self.assertFalse(alpha["currentSourceAuthorityPinnedAsFinal"])
        self.assertEqual(alpha["requiredEndOrdinal"], 97)


if __name__ == "__main__":
    unittest.main(verbosity=2)
