"""Regenerate ``pwpullwesetimpndv`` with an identity-safe dependency cache.

The historical generic deduction transformer cached dependencies by bare
``id(Node)`` values without retaining the Nodes.  CPython could therefore
reuse an id and return an unrelated cached dependency set.  In this proof it
misclassified a ``pm2.43i`` subtree and emitted the discharged hypothesis
``pwpullwesetndv.1`` outside its scope.

This generator executes an in-memory patched copy of the transformer.  The
patch retains every Node whose id is used as a cache key and asserts identity
on cache hits.  The shared transformer and all source proof files are left
unchanged.
"""

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
    "fixed_type_lowering/hartogs_invariance/hn_code_transport_live.mm"
)
PRE = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else DEFAULT_PRE
OUTPUT = (
    Path(sys.argv[2]).resolve()
    if len(sys.argv) > 2
    else HERE / "pwpullwesetimp_scope_clean_proof.txt"
)


def patched_transformer_source() -> str:
    source = TRANSFORMER.read_text(encoding="utf-8")
    source, count = source.replace(
        "dependency_cache = {}\n",
        "dependency_cache = {}\n"
        "dependency_cache_nodes = {}  # retain identity keys; prevent id reuse\n",
        1,
    ), source.count("dependency_cache = {}\n")
    if count != 1:
        raise RuntimeError(f"unexpected dependency-cache declarations: {count}")

    old = """    if root_key in dependency_cache:
        return dependency_cache[root_key]
"""
    new = """    if root_key in dependency_cache:
        assert dependency_cache_nodes[root_key] is node
        return dependency_cache[root_key]
"""
    if source.count(old) != 1:
        raise RuntimeError("root cache-hit block changed")
    source = source.replace(old, new, 1)

    old = """        if key in dependency_cache:
            continue
"""
    new = """        if key in dependency_cache:
            assert dependency_cache_nodes[key] is current
            continue
"""
    if source.count(old) != 1:
        raise RuntimeError("DFS cache-hit block changed")
    source = source.replace(old, new, 1)

    old = """        if hasattr(obj, "var"):
            dependency_cache[key] = (
"""
    new = """        if hasattr(obj, "var"):
            dependency_cache_nodes[key] = current
            dependency_cache[key] = (
"""
    if source.count(old) != 1:
        raise RuntimeError("leaf cache-write block changed")
    source = source.replace(old, new, 1)

    old = """            dependency_cache[key] = frozenset(found)
            continue
"""
    new = """            dependency_cache_nodes[key] = current
            dependency_cache[key] = frozenset(found)
            continue
"""
    if source.count(old) != 1:
        raise RuntimeError("internal cache-write block changed")
    source = source.replace(old, new, 1)
    return source


def main() -> int:
    source = patched_transformer_source()
    old_argv = sys.argv
    sys.argv = [
        str(TRANSFORMER),
        str(PRE),
        "pwpullwesetndv",
        "pwpullwesetimpndv",
        "pwpullwesetndv.1,pwpullwesetndv.2",
    ]
    captured = io.StringIO()
    module_name = "pwpull_scope_clean_transform"
    module = types.ModuleType(module_name)
    module.__file__ = str(TRANSFORMER)
    module.__package__ = None
    sys.modules[module_name] = module
    try:
        with redirect_stdout(captured):
            exec(compile(source, str(TRANSFORMER), "exec"), module.__dict__)
    finally:
        sys.argv = old_argv

    lines = captured.getvalue().splitlines()
    theorem_line = next(
        line for line in lines if line.startswith("pwpullwesetimpndv $= ")
    )
    prefix = "pwpullwesetimpndv $= "
    suffix = " $."
    if not theorem_line.endswith(suffix):
        raise RuntimeError("generated theorem line is not terminated")
    proof = theorem_line[len(prefix) : -len(suffix)]
    if "pwpullwesetndv.1" in proof or "pwpullwesetndv.2" in proof:
        raise RuntimeError("generated proof still names a discharged hypothesis")
    OUTPUT.write_text(proof + "\n", encoding="utf-8", newline="\n")
    for line in lines:
        if line.startswith("expanded="):
            print(line)
    print(f"wrote {OUTPUT} ({OUTPUT.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
