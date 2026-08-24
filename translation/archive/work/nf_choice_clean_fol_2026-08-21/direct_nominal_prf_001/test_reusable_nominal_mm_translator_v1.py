#!/usr/bin/env python3
"""Small source-only unit tests for reusable_nominal_mm_translator_v1.

These tests parse and proof-check a six-statement synthetic Metamath database
and exercise only deterministic selection/partition/contract helpers.  They do
not import Lean, invoke Lean, or emit the WPP closure.
"""

from __future__ import annotations

from contextlib import contextmanager
import json
from pathlib import Path
import shutil
import subprocess
import sys
import unittest
import uuid


HERE = Path(__file__).resolve().parent
CHOICE_COMPILER = HERE.parent / "compiler"
for root in (HERE, CHOICE_COMPILER):
    value = str(root)
    if value not in sys.path:
        sys.path.insert(0, value)

import reusable_nominal_mm_translator_v1 as cli
import compact_fv_normalize_mixin_v1 as compact_fv
from mm_parser import Database, tokenize_text


MINIMAL_MM = HERE / "testdata" / "reusable_nominal_mm_translator_tiny.mm"
PREFIX49_RESOURCE = HERE / "a49op1r1" / "resource.json"
PREFIX49_RESOURCE_SHA256 = (
    "7F2367A3D5ED3D82836028A6258440CF0CD3E0FD31388E6CBC775590ACAE43D2"
)


@contextmanager
def writable_test_directory():  # type: ignore[no-untyped-def]
    """Avoid Windows tempfile's sandbox-inaccessible mode-700 ACL."""

    root = HERE / f".translator-test-{uuid.uuid4().hex}"
    root.mkdir(parents=False, exist_ok=False)
    try:
        yield str(root)
    finally:
        shutil.rmtree(root)


class ParserSelectionTests(unittest.TestCase):
    def test_checked_database_and_endpoint_closure_interval(self) -> None:
        database = Database()
        database.parse(MINIMAL_MM)
        closure = database.dependency_closure("th2")
        labels = [
            statement.label for statement in closure
            if statement.kind == "$p" and statement.typecode == "|-"
        ]
        self.assertEqual(labels, ["th1", "th2"])
        selected = cli.select_interval(labels, 2, 2)
        self.assertEqual(selected.start_ordinal, 2)
        self.assertEqual(selected.end_ordinal, 2)
        self.assertEqual(selected.earlier_labels, ("th1",))
        self.assertEqual(selected.selected_labels, ("th2",))

    def test_interval_requires_both_bounds(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "supplied together"):
            cli.select_interval(["a"], 1, None)
        with self.assertRaisesRegex(RuntimeError, "1 <= start"):
            cli.select_interval(["a", "b"], 2, 3)


class PartitionTests(unittest.TestCase):
    def test_greedy_whole_theorem_partition_and_large_singleton(self) -> None:
        blocks = (b"aaa", b"bbbb", b"123456789", b"zz")
        groups = cli.group_blocks(blocks, 6)
        self.assertEqual(groups, ((0, 1), (1, 2), (2, 3), (3, 4)))
        self.assertGreater(len(blocks[2]), 6)
        self.assertTrue(all(end - begin == 1 for begin, end in groups))
        reconstructed = tuple(
            block for begin, end in groups for block in blocks[begin:end]
        )
        self.assertEqual(reconstructed, blocks)

    def test_source_artifacts_reconstruct_blocks(self) -> None:
        blocks = (b"noncomputable def g_a := by exact True.intro\n\n",
                  b"noncomputable def g_b := by exact True.intro\n\n")
        emission = cli.Emission(
            blocks=blocks,
            theorem_records=(),
            trace=(),
            cache_census={
                "total": 0, "nonmembership": 0, "inequality": 0, "disjoint": 0
            },
            compact_fv_normalization_count=0,
            generic_dv_fallback_count=0,
        )
        selection = cli.select_interval(["a", "b"], None, None)
        frontier = type("Frontier", (), {"imports": ("NominalDfEu",)})()
        output = Path("C:/source-only/unit-output")
        parts, umbrella, files = cli.build_source_artifacts(
            emission,
            selection,
            frontier,
            "UnitReplay",
            cli.DEFAULT_NAMESPACE,
            len(blocks[0]),
            None,
            output,
        )
        self.assertEqual(len(parts), 2)
        self.assertIsNone(parts[0]["predecessor"])
        self.assertEqual(parts[1]["predecessor"], "UnitReplayPart001")
        self.assertEqual(umbrella["imports"], "UnitReplayPart002")
        copied = [parts[0]["copiedTheoremSha256"], parts[1]["copiedTheoremSha256"]]
        self.assertEqual(copied, [cli.sha256_bytes(block) for block in blocks])
        self.assertEqual(len(files), 3)


class CompactFVBackendTests(unittest.TestCase):
    class Node:
        def __init__(
            self,
            sort: str,
            name: str,
            *,
            variable: bool,
            support: tuple | None = None,
        ) -> None:
            self.sort = sort
            self.variable_name = name
            self.is_variable = variable
            self.support = support

    class StructuralHost:
        compact_fv_error_type = RuntimeError

        def __init__(self, source_fact: tuple[str, bool] | None) -> None:
            self._current_local_sorts: dict[str, str] = {}
            self.source_fact = source_fact

        def fv_lemmas(self, _tree):  # type: ignore[no-untyped-def]
            return ("fv_syn_unit",)

        def _head_fv_support(self, tree):  # type: ignore[no-untyped-def]
            return "fv_syn_unit", tree.support

        def _source_dv_fact(self, _left, _right):  # type: ignore[no-untyped-def]
            return self.source_fact

        def qualified_expr(self, tree):  # type: ignore[no-untyped-def]
            return tree.variable_name

        def structural_dv_tactic(self, _left, _right):  # type: ignore[no-untyped-def]
            return "inherited-structural"

    class Emitter(compact_fv.CompactFVNormalizeMixin, StructuralHost):
        pass

    def test_alpha_neutral_mixin_emits_one_fail_closed_normalizer(self) -> None:
        x = self.Node("setvar", "x", variable=True)
        y = self.Node("setvar", "y", variable=True)
        term = self.Node(
            "class", "term", variable=False,
            support=("singleton_tree", y),
        )
        emitter = self.Emitter(("dv_x_y", False))
        tactic = emitter.structural_dv_tactic(x, term)
        self.assertEqual(tactic.count("simp only ["), 1)
        self.assertIn("dv_x_y", tactic)
        self.assertIn("compact_fv_not_mem_empty", tactic)
        self.assertNotIn("aesop", tactic)
        self.assertNotIn("assumption", tactic)
        self.assertEqual(
            emitter.structural_dv_tactic(x, y), "inherited-structural"
        )

    def test_alpha_neutral_mixin_missing_atomic_fact_fails_closed(self) -> None:
        x = self.Node("setvar", "x", variable=True)
        y = self.Node("setvar", "y", variable=True)
        term = self.Node(
            "class", "term", variable=False,
            support=("singleton_tree", y),
        )
        with self.assertRaisesRegex(RuntimeError, "missing atomic source DV"):
            self.Emitter(None).structural_dv_tactic(x, term)

    def test_emit_selection_audits_a_real_structural_cache_marker(self) -> None:
        class FakeEmitter:
            def __init__(self) -> None:
                self.trace: list[dict[str, object]] = []

            def emit_theorem(self, label, _available):  # type: ignore[no-untyped-def]
                return (
                    f"noncomputable def g_{label} := by\n"
                    "  have dv_cache_0001 : x ∉ A.fv := by\n"
                    "    exact (by\n"
                    "      have compact_fv_not_mem_empty : "
                    "x ∉ (∅ : Finset Var) := by\n"
                    "        intro hmem\n"
                    "        cases hmem\n"
                    "      simp only [compact_fv_not_mem_empty])\n"
                    "  exact True.intro"
                )

        statement = type("Statement", (), {"proof_ops": ()})()
        database = type("FakeDatabase", (), {"statements": {"unit": statement}})()
        selection = cli.select_interval(["unit"], None, None)
        emission = cli.emit_selection(FakeEmitter(), database, selection)
        self.assertEqual(emission.cache_census["nonmembership"], 1)
        self.assertEqual(emission.compact_fv_normalization_count, 1)
        self.assertEqual(
            emission.theorem_records[0]["compactFvNormalizationCount"], 1
        )


class ContractTests(unittest.TestCase):
    def test_real_prefix49_recovers_recursive_reflected_imports(self) -> None:
        script = (
            "import json,sys;"
            f"sys.path.insert(0,{str(HERE)!r});"
            "import reusable_nominal_mm_translator_v1 as c;"
            "b=c.load_backend('WPP_PROFILE_V2');"
            f"f,_=c.load_alpha_frontier(b,c.Path({str(PREFIX49_RESOURCE)!r}),"
            f"{PREFIX49_RESOURCE_SHA256!r});"
            "print(json.dumps({'verified':f.recursive_override_contract_verified,"
            "'changed':f.recursive_override_changed_count,'imports':f.imports}))"
        )
        run = subprocess.run(
            [sys.executable, "-B", "-c", script],
            cwd=HERE.parents[2],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        payload = json.loads(run.stdout)
        imports = payload["imports"]
        self.assertTrue(payload["verified"])
        self.assertEqual(payload["changed"], 15)
        self.assertEqual(
            imports[33],
            "NominalAlphaRepairedBase001034OpReflected001",
        )
        self.assertEqual(
            imports[36],
            "NominalAlphaRepairedBase001037OpabOpaqueHoisted004",
        )
        self.assertEqual(
            imports[47],
            "NominalAlphaRepairedBase001048Leaf2ndReflected001",
        )
        self.assertEqual(
            imports[48],
            "NominalAlphaRepairedBase001049OprabReflected001",
        )

    @staticmethod
    def write_resource(path: Path, data: object) -> str:
        path.write_bytes(cli.json_bytes(data))
        return cli.sha256(path)

    def test_translator_source_resource_is_its_own_predecessor(self) -> None:
        with writable_test_directory() as temporary:
            root = Path(temporary)
            source = root / "Replay17.lean"
            source.write_bytes(b"import Base\n")
            data = {
                "schema": "nf-reusable-nominal-mm-translator-v1",
                "status": "PASS_SOURCE_ONLY_EMITTED_STRUCTURAL",
                "sourceSha256": "B" * 64,
                "endpoint": "goal",
                "endTheoremOrdinal": 17,
                "umbrellaModule": {
                    "module": "Replay17",
                    "source": str(source),
                    "sourceSha256": cli.sha256(source),
                },
            }
            resource = root / "resource.json"
            pin = self.write_resource(resource, data)
            contract = cli.load_predecessor(
                resource, pin, "B" * 64, "goal", 17
            )
            self.assertEqual(contract.end_theorem_ordinal, 17)
            self.assertEqual(contract.module, "Replay17")
            self.assertEqual(contract.boundary_kind, "source-only")
            self.assertEqual(contract.source_artifact, source.resolve())
            self.assertIsNone(contract.kernel_artifact)

            source.write_bytes(b"tampered\n")
            with self.assertRaisesRegex(RuntimeError, "umbrella source artifact"):
                cli.load_predecessor(resource, pin, "B" * 64, "goal", 17)

    def test_snake_case_source_resource_requires_hashed_artifact(self) -> None:
        with writable_test_directory() as temporary:
            root = Path(temporary)
            source = root / "Replay25.lean"
            source.write_bytes(b"import Replay24\n")
            data = {
                "status": "GENERATED_SOURCE_ONLY_LOSSLESS",
                "exact_wpp_source_sha256": "C" * 64,
                "endpoint": "goal",
                "end_theorem_ordinal": 25,
                "umbrella_module": {
                    "module": "Replay25",
                    "source": str(source),
                    "source_sha256": cli.sha256(source),
                },
            }
            resource = root / "legacy-source.json"
            pin = self.write_resource(resource, data)
            contract = cli.load_predecessor(
                resource, pin, "C" * 64, "goal", 25
            )
            self.assertEqual(contract.module, "Replay25")
            self.assertEqual(contract.boundary_kind, "source-only")

    def test_kernel_predecessor_verifies_source_and_olean_separately(self) -> None:
        with writable_test_directory() as temporary:
            root = Path(temporary)
            source = root / "Replay31.lean"
            source.write_bytes(b"import Replay30\n")
            source_data = {
                "status": "PASS_SOURCE_ONLY_EMITTED_STRUCTURAL",
                "sourceSha256": "D" * 64,
                "endpoint": "goal",
                "endTheoremOrdinal": 31,
                "umbrellaModule": {
                    "module": "Replay31",
                    "source": str(source),
                    "sourceSha256": cli.sha256(source),
                },
            }
            source_resource = root / "source-resource.json"
            source_pin = self.write_resource(source_resource, source_data)
            olean = root / "Replay31.olean"
            olean.write_bytes(b"synthetic kernel artifact for schema test\n")
            kernel_data = {
                "status": "PASS_TRUST0_UMBRELLA_EXACT_THREE",
                "splitResource": str(source_resource),
                "splitResourceSha256": source_pin,
                "exactWppSourceSha256": "D" * 64,
                "umbrellaCommand": {
                    "module": "Replay31",
                    "trust": 0,
                    "source": str(source),
                    "sourceSha256": cli.sha256(source),
                    "exitCode": 0,
                    "killed": False,
                    "exactAllowedThree": True,
                    "output": str(olean),
                    "outputSha256": cli.sha256(olean),
                },
            }
            kernel_resource = root / "kernel-resource.json"
            kernel_pin = self.write_resource(kernel_resource, kernel_data)
            contract = cli.load_predecessor(
                kernel_resource, kernel_pin, "D" * 64, "goal", 31
            )
            self.assertEqual(
                contract.boundary_kind, "kernel-trust-zero-exact-three"
            )
            self.assertEqual(contract.source_artifact, source.resolve())
            self.assertEqual(contract.kernel_artifact, olean.resolve())

            olean.write_bytes(b"tampered\n")
            with self.assertRaisesRegex(RuntimeError, "kernel umbrella output"):
                cli.load_predecessor(
                    kernel_resource, kernel_pin, "D" * 64, "goal", 31
                )

    def test_hash_module_and_alpha_exact_three_validation(self) -> None:
        self.assertEqual(cli.normalized_sha256("a" * 64, "unit"), "A" * 64)
        with self.assertRaisesRegex(RuntimeError, "invalid unit"):
            cli.normalized_sha256("xyz", "unit")
        self.assertEqual(cli.require_module_name("A.B_2", "module"), "A.B_2")
        with self.assertRaisesRegex(RuntimeError, "invalid Lean"):
            cli.require_module_name("A/b", "module")
        resource = {
            "audit": {
                "exactAllowedThreeAll": True,
                "axiomReports": [
                    {"theorem": "t", "axioms": list(cli.ALLOWED_AXIOMS)}
                ],
            }
        }
        self.assertTrue(cli.exact_three_alpha_resource(resource))
        resource["audit"]["axiomReports"][0]["axioms"].append("sorryAx")
        self.assertFalse(cli.exact_three_alpha_resource(resource))
        self.assertFalse(cli.exact_three_alpha_resource({
            "audit": {"exactAllowedThree": True}
        }))
        self.assertTrue(cli.exact_three_alpha_resource({
            "audit": {
                "exactAllowedThree": True,
                "reportedAxioms": list(cli.ALLOWED_AXIOMS),
            }
        }))
        compact_resource = {
            "allowedAxioms": list(cli.ALLOWED_AXIOMS),
            "audit": {
                "exactAllowedThreeAll": True,
                "exitCode": 0,
                "killed": False,
                "emptyStderr": True,
                "forbiddenAxiomMatches": [],
            },
        }
        self.assertTrue(cli.exact_three_alpha_resource(compact_resource))
        for field, bad_value in (
            ("exitCode", 1),
            ("killed", True),
            ("emptyStderr", False),
            ("forbiddenAxiomMatches", ["sorryAx"]),
        ):
            rejected = json.loads(json.dumps(compact_resource))
            rejected["audit"][field] = bad_value
            self.assertFalse(cli.exact_three_alpha_resource(rejected))
        compact_resource["allowedAxioms"].append("sorryAx")
        self.assertFalse(cli.exact_three_alpha_resource(compact_resource))

    def test_unsupported_leaf_fails_before_any_output(self) -> None:
        with writable_test_directory() as temporary:
            root = Path(temporary)
            output = root / "not-created"
            staging = root / ".not-created.staging-v1"
            missing = [{"theorem": "goal", "leaf": "unsupported"}]
            with self.assertRaisesRegex(
                RuntimeError, "unsupported leaf at selected frontier"
            ):
                cli.require_supported_leaf_coverage(missing)
            self.assertFalse(output.exists())
            self.assertFalse(staging.exists())

    def test_v1_rejects_real_metamath_includes_but_not_comments(self) -> None:
        cli.require_no_metamath_includes(tokenize_text(
            "$( a comment containing $[ child.mm $] $) $c |- $."
        ))
        with self.assertRaisesRegex(RuntimeError, "includes are unsupported"):
            cli.require_no_metamath_includes(tokenize_text(
                "$[ child.mm $] $c |- $."
            ))

    def test_cache_census_and_forbidden_scan(self) -> None:
        source = (
            "  have dv_cache_0001 : x ∉ A.fv := by\n"
            "  have dv_cache_0002 : x ≠ y := by\n"
            "  have dv_cache_0003 : Disjoint A.fv B.fv := by\n"
        ).encode("utf-8")
        self.assertEqual(
            cli.cache_census(source),
            {"total": 3, "nonmembership": 1, "inequality": 1, "disjoint": 1},
        )
        self.assertIsNotNone(cli.FORBIDDEN_SOURCE_RE.search(b"axiom bad : True"))
        self.assertIsNone(cli.FORBIDDEN_SOURCE_RE.search(source))


if __name__ == "__main__":
    unittest.main(verbosity=2)
