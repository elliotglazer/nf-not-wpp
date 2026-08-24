"""Regenerate ``hnqinctrnvaldndv`` with an identity-safe dependency cache."""

from __future__ import annotations

from contextlib import redirect_stdout
import io
from pathlib import Path
import sys
import types


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[3]
TRANSFORMER = (
    WORKSPACE
    / "work/formalization_continue/wellorder_comparison/"
    "build_wellorder_comparison_terminal_pair_deduction.py"
)
DEFAULT_PRE = (
    WORKSPACE
    / "work/formalization_continue/concrete_orbit_specialization/"
    "fixed_type_lowering/hartogs_invariance/quotient_common_range/"
    "hn_qinc_transport_conditional_pre.mm"
)
PRE = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else DEFAULT_PRE
OUTPUT = (
    Path(sys.argv[2]).resolve()
    if len(sys.argv) > 2
    else HERE / "hnqinctrnvaldndv_scope_clean_proof.txt"
)


def patched_transformer_source() -> str:
    source = TRANSFORMER.read_text(encoding="utf-8")
    needle = "dependency_cache = {}\n"
    if source.count(needle) != 1:
        raise RuntimeError("dependency-cache declaration changed")
    source = source.replace(
        needle,
        needle + "dependency_cache_nodes = {}  # retain identity cache keys\n",
        1,
    )

    replacements = (
        (
            """    if root_key in dependency_cache:
        return dependency_cache[root_key]
""",
            """    if root_key in dependency_cache:
        assert dependency_cache_nodes[root_key] is node
        return dependency_cache[root_key]
""",
        ),
        (
            """        if key in dependency_cache:
            continue
""",
            """        if key in dependency_cache:
            assert dependency_cache_nodes[key] is current
            continue
""",
        ),
        (
            """        if hasattr(obj, "var"):
            dependency_cache[key] = (
""",
            """        if hasattr(obj, "var"):
            dependency_cache_nodes[key] = current
            dependency_cache[key] = (
""",
        ),
        (
            """            dependency_cache[key] = frozenset(found)
            continue
""",
            """            dependency_cache_nodes[key] = current
            dependency_cache[key] = frozenset(found)
            continue
""",
        ),
    )
    for old, new in replacements:
        if source.count(old) != 1:
            raise RuntimeError("transformer dependency block changed")
        source = source.replace(old, new, 1)
    return source


def main() -> int:
    source = patched_transformer_source()
    old_argv = sys.argv
    sys.argv = [
        str(TRANSFORMER),
        str(PRE),
        "hnqinctrnvalndv",
        "hnqinctrnvaldndv",
        "hnqinctrnvalndv.6",
    ]
    module_name = "hnqinc_scope_clean_transform"
    module = types.ModuleType(module_name)
    module.__file__ = str(TRANSFORMER)
    module.__package__ = None
    sys.modules[module_name] = module
    captured = io.StringIO()
    try:
        with redirect_stdout(captured):
            exec(compile(source, str(TRANSFORMER), "exec"), module.__dict__)
    finally:
        sys.argv = old_argv

    lines = captured.getvalue().splitlines()
    prefix = "hnqinctrnvaldndv $= "
    theorem_line = next(line for line in lines if line.startswith(prefix))
    if not theorem_line.endswith(" $."):
        raise RuntimeError("generated theorem line is not terminated")
    proof = theorem_line[len(prefix) : -3]
    if "hnqinctrnvalndv.6" in proof:
        raise RuntimeError("generated proof still names the discharged hypothesis")
    OUTPUT.write_text(proof + "\n", encoding="utf-8", newline="\n")
    for line in lines:
        if line.startswith("expanded="):
            print(line)
    print(f"wrote {OUTPUT} ({OUTPUT.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
