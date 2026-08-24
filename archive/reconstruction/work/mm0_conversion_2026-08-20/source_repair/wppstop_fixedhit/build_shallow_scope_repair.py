"""Build a proof-only, shallow scope repair for the stopped fixed-hit theorem.

This does not perform a recursive deduction transform.  It instantiates the
already-verified equality-dependent donor proof once, replacing its twelve
essential leaves by constant-size conditional-class proofs, and then
recompresses the resulting shared DAG.
"""

from __future__ import annotations

import gc
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BASE = (
    HERE.parents[1]
    / "toolchain/cfb_codecover_scope_repair"
    / "endpoint_after_cfb_codecover_frozen_checkpoint.mm"
)
DONOR = (
    ROOT
    / "work/formalization_continue/stopped_gamma_fixed_start"
    / "witness_free_contradiction"
    / "stopped_fixed_hit_package_growth_adapters_deduction_live.mm"
)
BUILDER = ROOT / "formalization_continue/reconstruct/mmproof_builder_current.py"
PRE = HERE / "wppstopfixedhit_shallow_pre.mm"
OUT = HERE / "endpoint_after_cfb_codecover_wppstopfixedhit_scope_repaired.mm"
REPORT = HERE / "wppstopfixedhit_scope_repair_report.json"
DELTA = HERE / "wppstopfixedhit_scope_repair.delta.json"
PROOF = HERE / "wppstopfixedhitcontrgrowfixdndv_scope_clean_proof.txt"

SOURCE = "wppstopfixedhitcontrgrowadaptdndv"
TARGET = "wppstopfixedhitcontrgrowfixdndv"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest().upper()


def flat(*parts):
    out: list[str] = []
    for part in parts:
        if isinstance(part, tuple):
            out.extend(part)
        else:
            out.append(part)
    return tuple(out)


def atom(name):
    return (name,)


def mem(left, right):
    return flat(left, "e.", right)


def eq(left, right):
    return flat(left, "=", right)


def conj(left, right):
    return flat("(", left, "/\\", right, ")")


def imp(left, right):
    return flat("(", left, "->", right, ")")


def neg(body):
    return flat("-.", body)


def tc(body):
    return flat("T_c", body)


def cif(condition, yes, no):
    return flat("if", "(", condition, ",", yes, ",", no, ")")


def nc(body):
    return flat("Nc", body)


def dm(body):
    return flat("dom", body)


def rn(body):
    return flat("ran", body)


def fv(fun, arg):
    return flat("(", fun, "`", arg, ")")


def step(fun, threshold):
    return flat("WPPStopStep", "(", fun, ",", threshold, ")")


def hit(fun, start, threshold):
    return flat("WPPHit", "(", fun, ",", start, ",", threshold, ")")


def rall(var, domain, body):
    return flat("A.", var, "e.", domain, body)


def ex(var, body):
    return flat("E.", var, body)


def cardle(left, right):
    return flat(left, "<_c", right)


def finle(left, right):
    return flat(left, "KQRel", "<_[fin]", right)


def we(rel, base):
    return flat(rel, "We", base)


def package(index, fun, start, threshold):
    hit_class = hit(fun, start, threshold)
    minimal = rall(
        atom("n"),
        atom("Nn"),
        imp(mem(atom("n"), hit_class), finle(index, atom("n"))),
    )
    return conj(mem(index, atom("Nn")), conj(mem(index, hit_class), minimal))


class Node:
    __slots__ = ("label", "args", "replacement")

    def __init__(self, label: str, args=()):
        self.label = label
        self.args = tuple(args)
        self.replacement: Node | None = None


def source_dag(raw_db, statement):
    if statement.proof and statement.proof[0] == "(":
        labels, sequence = raw_db._decode_compressed(list(statement.proof), statement)
    else:
        labels, sequence = (), list(statement.proof)
    stack: list[Node] = []
    saved: list[Node] = []
    all_nodes: list[Node] = []
    for number in sequence:
        if number == -1:
            saved.append(stack[-1])
            continue
        if isinstance(number, int) and number >= len(labels):
            stack.append(saved[number - len(labels)])
            continue
        label = labels[number] if isinstance(number, int) else number
        obj = raw_db.labels[label]
        if hasattr(obj, "var"):
            node = Node(label)
        else:
            arity = len(obj.hyps)
            args = tuple(stack[-arity:]) if arity else ()
            if arity:
                del stack[-arity:]
            node = Node(label, args)
        stack.append(node)
        all_nodes.append(node)
    assert len(stack) == 1
    return stack[0], all_nodes


def postorder_unique(root: Node) -> list[Node]:
    """Return the reachable DAG nodes with every child before its parents."""
    order: list[Node] = []
    seen: set[int] = set()
    stack: list[tuple[Node, bool]] = [(root, False)]
    while stack:
        node, exiting = stack.pop()
        key = id(node)
        if exiting:
            order.append(node)
            continue
        if key in seen:
            continue
        seen.add(key)
        stack.append((node, True))
        for arg in reversed(node.args):
            stack.append((arg, False))
    return order


def instantiate_template(
    template_root: Node,
    template_nodes: list[Node],
    hypothesis_map: dict[str, Node],
) -> Node:
    """Instantiate one already-decoded proof DAG at its mandatory hypotheses."""
    replacements: dict[int, Node] = {}
    for node in template_nodes:
        if node.label in hypothesis_map:
            replacements[id(node)] = hypothesis_map[node.label]
        else:
            replacements[id(node)] = Node(
                node.label,
                tuple(replacements[id(arg)] for arg in node.args),
            )
    return replacements[id(template_root)]


def compressed(db, label: str, root: Node):
    refcount: dict[int, int] = {}
    visited: set[int] = set()
    stack = [root]
    while stack:
        current = stack.pop()
        key = id(current)
        refcount[key] = refcount.get(key, 0) + 1
        if key in visited:
            continue
        visited.add(key)
        stack.extend(reversed(current.args))

    symbolic: list[tuple[str, object]] = []
    saved: dict[int, int] = {}
    emit_stack = [(root, False)]
    while emit_stack:
        current, exiting = emit_stack.pop()
        key = id(current)
        if key in saved:
            symbolic.append(("ref", saved[key]))
            continue
        if exiting:
            symbolic.append(("label", current.label))
            if refcount[key] > 1:
                saved[key] = len(saved)
                symbolic.append(("save", None))
            continue
        emit_stack.append((current, True))
        for arg in reversed(current.args):
            emit_stack.append((arg, False))

    mandatory = list(db.stmts[label].mand_hyps)
    extras: list[str] = []
    for kind, value in symbolic:
        if kind == "label" and value not in mandatory and value not in extras:
            extras.append(value)  # type: ignore[arg-type]
    stale = [item for item in extras if item.startswith(SOURCE + ".")]
    assert not stale, stale
    table = mandatory + extras

    def encode(number: int) -> str:
        last = chr(ord("A") + (number - 1) % 20)
        number = (number - 1) // 20
        prefix = ""
        while number:
            number, remainder = divmod(number - 1, 5)
            prefix = chr(ord("U") + remainder) + prefix
        return prefix + last

    code: list[str] = []
    for kind, value in symbolic:
        if kind == "save":
            code.append("Z")
        elif kind == "label":
            code.append(encode(table.index(value) + 1))
        else:
            code.append(encode(len(table) + int(value) + 1))
    return f"( {' '.join(extras)} ) {''.join(code)}", len(visited), len(saved)


def make_pre() -> None:
    text = BASE.read_text(encoding="utf-8")
    start = text.index(TARGET + " $p")
    proof_start = text.index("$=", start)
    proof_end = text.index("$.", proof_start) + 2
    text = text[:proof_start] + "$= ? $." + text[proof_end:]
    PRE.write_text(text, encoding="utf-8", newline="\n")


def main() -> None:
    make_pre()

    spec = importlib.util.spec_from_file_location("wppstop_shallow_builder", BUILDER)
    assert spec is not None and spec.loader is not None
    mpb = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mpb
    spec.loader.exec_module(mpb)

    donor_db = mpb.load(DONOR, verify=False, allow_incomplete=False)
    donor_statement = donor_db.raw.labels[SOURCE]
    donor_root, donor_nodes = source_dag(donor_db.raw, donor_statement)

    # The frozen endpoint deliberately sliced away four local convenience
    # theorems used by the donor.  Expand precisely those applications once.
    # This is a bounded proof splice (not a recursive deduction transform).
    shallow_labels = (
        "wpphitstartfix",
        "frecstartfix",
        "mt2i",
        "wpphitshiftptndv",
    )
    shallow_expansions: dict[str, int] = {}
    for shallow_label in shallow_labels:
        shallow_statement = donor_db.raw.labels[shallow_label]
        shallow_root, shallow_nodes = source_dag(
            donor_db.raw, shallow_statement
        )
        shallow_hyps = tuple(shallow_statement.hyps)
        applications = 0
        for node in postorder_unique(donor_root):
            if node.label != shallow_label:
                continue
            if len(node.args) != len(shallow_hyps):
                raise ValueError(
                    f"unexpected {shallow_label} application arity"
                )
            expanded = instantiate_template(
                shallow_root,
                shallow_nodes,
                dict(zip(shallow_hyps, node.args)),
            )
            node.label = expanded.label
            node.args = expanded.args
            applications += 1
        if not applications:
            raise ValueError(f"donor did not use {shallow_label}")
        shallow_expansions[shallow_label] = applications
    donor_nodes = postorder_unique(donor_root)

    floating_var: dict[str, tuple[str, str]] = {}
    for node in donor_nodes:
        obj = donor_db.raw.labels[node.label]
        if hasattr(obj, "var") and obj.kind == "$f":
            floating_var[node.label] = (obj.expr[0], obj.var)
    donor_node_count = len({id(node) for node in donor_nodes})
    del donor_db
    gc.collect()

    db = mpb.load(PRE, verify=True, allow_incomplete=True)
    builder = mpb.Builder(db)

    def node_from_sequence(sequence):
        stack: list[Node] = []
        for label in sequence:
            obj = db.raw.labels[label]
            if hasattr(obj, "var"):
                stack.append(Node(label))
                continue
            arity = len(obj.hyps)
            args = tuple(stack[-arity:]) if arity else ()
            if arity:
                del stack[-arity:]
            stack.append(Node(label, args))
        assert len(stack) == 1
        return stack[0]

    syntax_cache: dict[tuple[str, ...], Node] = {}

    def syntax_node(expression):
        expression = tuple(expression)
        if expression not in syntax_cache:
            proof = builder.syntax_proof(expression)
            if proof is None:
                raise ValueError(f"no syntax proof for {expression}")
            syntax_cache[expression] = node_from_sequence(proof)
        return syntax_cache[expression]

    def apn(label, subst=None, essentials=()):
        subst = subst or {}
        statement = db.stmts[label]
        essential_iter = iter(essentials)
        args: list[Node] = []
        for hyp_label in statement.mand_hyps:
            hyp = db.stmts[hyp_label]
            if hyp.kind == "$f":
                args.append(syntax_node(db.subst_expr(hyp.expr, subst)))
            else:
                args.append(next(essential_iter))
        try:
            next(essential_iter)
        except StopIteration:
            pass
        else:
            raise ValueError(f"too many essential proofs supplied to {label}")
        return Node(label, args), db.subst_expr(statement.expr, subst)

    def hyp(label):
        return Node(label), db.stmts[label].expr

    F = atom("F")
    C = atom("C")
    I = atom("I")
    ph = atom("ph")
    ps = atom("ps")
    ch = atom("ch")
    m = atom("m")
    k = atom("k")
    n = atom("n")
    d = atom("d")
    s = atom("s")
    zero = atom("0c")
    empty = atom("(/)")
    universe = atom("_V")
    hwcards = flat("HWCards", universe)
    tcI = tc(I)
    tcC = tc(C)
    E = eq(I, tcI)
    X = cif(E, I, zero)
    tcX = tc(X)
    P = conj(E, ph)
    Q = conj(E, ps)
    R = conj(E, ch)
    bottom = neg(eq(zero, zero))
    gamma = conj(ph, conj(ps, ch))
    target_body = imp(E, imp(gamma, bottom))

    fun0 = step(F, C)
    fun1 = step(F, tcC)
    pack0_I = package(m, fun0, I, C)
    pack0_X = package(m, fun0, X, C)
    pack1_I = package(k, fun1, tcI, tcC)
    pack1_X = package(k, fun1, tcX, tcC)
    growth = rall(
        atom("y"),
        dm(fun0),
        imp(cardle(tcC, atom("y")), cardle(C, fv(fun0, atom("y")))),
    )

    assert db.stmts[f"{TARGET}.7"].expr == ("|-",) + mem(I, hwcards)
    assert db.stmts[f"{TARGET}.10"].expr == ("|-",) + imp(ph, pack0_I)
    assert db.stmts[f"{TARGET}.11"].expr == ("|-",) + imp(ps, pack1_I)
    assert db.stmts[f"{TARGET}.12"].expr == ("|-",) + imp(ch, growth)
    assert db.stmts[TARGET].expr == ("|-",) + target_body

    # A retained empty well-order witnesses that 0c is in HWCards _V.
    cross_empty = flat("(", empty, "X.", empty, ")")
    empty_rel = flat("(", "KQRel", "<_[fin]", "i^i", cross_empty, ")")
    empty_we = we(empty_rel, empty)
    assert db.stmts["wecomparisondefaultemptywe"].expr == ("|-",) + empty_we
    p_empty_we, _ = apn("wecomparisondefaultemptywe")
    p_brex, brex_expr = apn(
        "brex", {"A": empty_rel, "R": atom("We"), "B": empty}
    )
    empty_sets = conj(mem(empty_rel, universe), mem(empty, universe))
    p_sets, _ = apn(
        "ax-mp",
        {"ph": empty_we, "ps": empty_sets},
        [p_empty_we, p_brex],
    )
    p_empty_rel_ex, _ = apn(
        "simpli",
        {"ph": mem(empty_rel, universe), "ps": mem(empty, universe)},
        [p_sets],
    )
    p_df0, _ = apn("df0c2")
    witness_formula = conj(empty_we, eq(zero, nc(empty)))
    p_witness, _ = apn(
        "pm3.2i",
        {"ph": empty_we, "ps": eq(zero, nc(empty))},
        [p_empty_we, p_df0],
    )

    pair_eq = conj(eq(d, empty), eq(s, empty_rel))
    p_d_eq, _ = apn("simpl", {"ph": eq(d, empty), "ps": eq(s, empty_rel)})
    p_s_eq, _ = apn("simpr", {"ph": eq(d, empty), "ps": eq(s, empty_rel)})
    p_we_bi, _ = apn(
        "breq12d",
        {
            "ph": pair_eq,
            "A": s,
            "B": empty_rel,
            "C": d,
            "D": empty,
            "R": atom("We"),
        },
        [p_s_eq, p_d_eq],
    )
    p_nc_eq, _ = apn(
        "nceqd", {"ph": pair_eq, "A": d, "B": empty}, [p_d_eq]
    )
    p_card_eq_bi, _ = apn(
        "eqeq2d",
        {"ph": pair_eq, "A": nc(d), "B": nc(empty), "C": zero},
        [p_nc_eq],
    )
    quantified_matrix = conj(we(s, d), eq(zero, nc(d)))
    p_matrix_bi, _ = apn(
        "anbi12d",
        {
            "ph": pair_eq,
            "ps": we(s, d),
            "ch": empty_we,
            "th": eq(zero, nc(d)),
            "ta": eq(zero, nc(empty)),
        },
        [p_we_bi, p_card_eq_bi],
    )
    exists_zero = ex(d, ex(s, conj(we(s, d), eq(zero, nc(d)))))
    p_exists_imp, exists_expr = apn(
        "spc2ev",
        {
            "x": d,
            "y": s,
            "A": empty,
            "B": empty_rel,
            "ph": quantified_matrix,
            "ps": witness_formula,
        },
        [
            apn("0ex")[0],
            p_empty_rel_ex,
            p_matrix_bi,
        ],
    )
    p_exists, _ = apn(
        "ax-mp",
        {"ph": witness_formula, "ps": exists_zero},
        [p_witness, p_exists_imp],
    )
    assert exists_expr == ("|-",) + imp(witness_formula, exists_zero)

    k0 = eq(k, zero)
    generic_exists = ex(d, ex(s, conj(we(s, d), eq(k, nc(d)))))
    generic_hw_bi = flat("(", mem(k, hwcards), "<->", generic_exists, ")")
    zero_hw_bi = flat("(", mem(zero, hwcards), "<->", exists_zero, ")")
    p_hw_mem_bi, _ = apn(
        "eleq1d",
        {"ph": k0, "A": k, "B": zero, "C": hwcards},
        [apn("id", {"ph": k0})[0]],
    )
    p_inner_eq_bi, _ = apn(
        "eqeq1d",
        {"ph": k0, "A": k, "B": zero, "C": nc(d)},
        [apn("id", {"ph": k0})[0]],
    )
    p_inner_matrix_bi, _ = apn(
        "anbi2d",
        {
            "ph": k0,
            "th": we(s, d),
            "ps": eq(k, nc(d)),
            "ch": eq(zero, nc(d)),
        },
        [p_inner_eq_bi],
    )
    p_ex_s_bi, _ = apn(
        "exbidv",
        {
            "ph": k0,
            "x": s,
            "ps": conj(we(s, d), eq(k, nc(d))),
            "ch": conj(we(s, d), eq(zero, nc(d))),
        },
        [p_inner_matrix_bi],
    )
    p_ex_d_bi, _ = apn(
        "exbidv",
        {
            "ph": k0,
            "x": d,
            "ps": ex(s, conj(we(s, d), eq(k, nc(d)))),
            "ch": ex(s, conj(we(s, d), eq(zero, nc(d)))),
        },
        [p_ex_s_bi],
    )
    p_generic_zero_bi, _ = apn(
        "bibi12d",
        {
            "ph": k0,
            "ps": mem(k, hwcards),
            "ch": mem(zero, hwcards),
            "th": generic_exists,
            "ta": exists_zero,
        },
        [p_hw_mem_bi, p_ex_d_bi],
    )
    p_elhwcardswev, elhwcardswev_expr = apn("elhwcardswev")
    assert elhwcardswev_expr == ("|-",) + generic_hw_bi
    p_zero_hw_bi_imp, _ = apn(
        "vtoclg",
        {
            "x": k,
            "A": zero,
            "V": universe,
            "ph": generic_hw_bi,
            "ps": zero_hw_bi,
        },
        [p_generic_zero_bi, p_elhwcardswev],
    )
    p_zero_hw_bi, _ = apn(
        "ax-mp",
        {"ph": mem(zero, universe), "ps": zero_hw_bi},
        [apn("0cex")[0], p_zero_hw_bi_imp],
    )
    p_zero_hw, _ = apn(
        "mpbir",
        {"ph": mem(zero, hwcards), "ps": exists_zero},
        [p_exists, p_zero_hw_bi],
    )

    # Conditional start class: a fixed HWCard in both truth branches.
    target_hyps = {i: hyp(f"{TARGET}.{i}")[0] for i in range(1, 8)}
    target_hyps.update({i: hyp(f"{TARGET}.{i}")[0] for i in range(9, 13)})
    p_hw_pair, _ = apn(
        "pm3.2i",
        {"ph": mem(I, hwcards), "ps": mem(zero, hwcards)},
        [target_hyps[7], p_zero_hw],
    )
    p_ifcl, ifcl_expr = apn(
        "ifcl", {"ph": E, "A": I, "B": zero, "C": hwcards}
    )
    p_X_hw, _ = apn(
        "ax-mp",
        {"ph": conj(mem(I, hwcards), mem(zero, hwcards)), "ps": mem(X, hwcards)},
        [p_hw_pair, p_ifcl],
    )
    assert ifcl_expr == ("|-",) + imp(
        conj(mem(I, hwcards), mem(zero, hwcards)), mem(X, hwcards)
    )

    p_iftrue, _ = apn("iftrue", {"ph": E, "A": I, "B": zero})
    p_tc_true_imp, _ = apn("tceq", {"A": X, "B": I})
    p_tc_true, _ = apn(
        "syl",
        {"ph": E, "ps": eq(X, I), "ch": eq(tcX, tcI)},
        [p_iftrue, p_tc_true_imp],
    )
    p_tc_true_rev, _ = apn(
        "eqcomd", {"ph": E, "A": tcX, "B": tcI}, [p_tc_true]
    )
    p_E, _ = apn("id", {"ph": E})
    p_fixed_true, _ = apn(
        "3eqtrd",
        {"ph": E, "A": X, "B": I, "C": tcI, "D": tcX},
        [p_iftrue, p_E, p_tc_true_rev],
    )

    notE = neg(E)
    p_iffalse, _ = apn("iffalse", {"ph": E, "A": I, "B": zero})
    p_tc_false_imp, _ = apn("tceq", {"A": X, "B": zero})
    p_tc_false, _ = apn(
        "syl",
        {"ph": notE, "ps": eq(X, zero), "ch": eq(tcX, tc(zero))},
        [p_iffalse, p_tc_false_imp],
    )
    p_tc_false_rev, _ = apn(
        "eqcomd",
        {"ph": notE, "A": tcX, "B": tc(zero)},
        [p_tc_false],
    )
    p_zero_tc0, _ = apn("eqcomi", {"A": tc(zero), "B": zero}, [apn("tc0c")[0]])
    p_zero_tc0_d, _ = apn(
        "a1i", {"ph": eq(zero, tc(zero)), "ps": notE}, [p_zero_tc0]
    )
    p_fixed_false, _ = apn(
        "3eqtrd",
        {"ph": notE, "A": X, "B": zero, "C": tc(zero), "D": tcX},
        [p_iffalse, p_zero_tc0_d, p_tc_false_rev],
    )
    p_X_fixed, _ = apn(
        "pm2.61i",
        {"ph": E, "ps": eq(X, tcX)},
        [p_fixed_true, p_fixed_false],
    )

    def transport_package(
        antecedent,
        original_formula,
        target_formula,
        original_start,
        target_start,
        fun,
        threshold,
        index,
        p_original,
        p_start_eq,
    ):
        old_hit = hit(fun, original_start, threshold)
        new_hit = hit(fun, target_start, threshold)
        p_congr_imp, _ = apn(
            "wpphitstartcongrndv",
            {"F": fun, "I": original_start, "J": target_start, "C": threshold},
        )
        p_hit_eq, _ = apn(
            "syl",
            {
                "ph": antecedent,
                "ps": eq(original_start, target_start),
                "ch": eq(old_hit, new_hit),
            },
            [p_start_eq, p_congr_imp],
        )
        p_index_hit_bi, _ = apn(
            "eleq2d",
            {"ph": antecedent, "A": old_hit, "B": new_hit, "C": index},
            [p_hit_eq],
        )
        p_n_hit_bi, _ = apn(
            "eleq2d",
            {"ph": antecedent, "A": old_hit, "B": new_hit, "C": n},
            [p_hit_eq],
        )
        p_imp_bi, _ = apn(
            "imbi1d",
            {
                "ph": antecedent,
                "ps": mem(n, old_hit),
                "ch": mem(n, new_hit),
                "th": finle(index, n),
            },
            [p_n_hit_bi],
        )
        old_min = rall(n, atom("Nn"), imp(mem(n, old_hit), finle(index, n)))
        new_min = rall(n, atom("Nn"), imp(mem(n, new_hit), finle(index, n)))
        p_ral_bi, _ = apn(
            "ralbidv",
            {
                "ph": antecedent,
                "x": n,
                "A": atom("Nn"),
                "ps": imp(mem(n, old_hit), finle(index, n)),
                "ch": imp(mem(n, new_hit), finle(index, n)),
            },
            [p_imp_bi],
        )
        p_inner_bi, _ = apn(
            "anbi12d",
            {
                "ph": antecedent,
                "ps": mem(index, old_hit),
                "ch": mem(index, new_hit),
                "th": old_min,
                "ta": new_min,
            },
            [p_index_hit_bi, p_ral_bi],
        )
        p_package_bi, _ = apn(
            "anbi2d",
            {
                "ph": antecedent,
                "th": mem(index, atom("Nn")),
                "ps": conj(mem(index, old_hit), old_min),
                "ch": conj(mem(index, new_hit), new_min),
            },
            [p_inner_bi],
        )
        p_target, expr = apn(
            "mpbid",
            {"ph": antecedent, "ps": original_formula, "ch": target_formula},
            [p_original, p_package_bi],
        )
        assert expr == ("|-",) + imp(antecedent, target_formula)
        return p_target

    p_P_ph, _ = apn("simpr", {"ph": E, "ps": ph})
    p_P_pack0I, _ = apn(
        "syl",
        {"ph": P, "ps": ph, "ch": pack0_I},
        [p_P_ph, target_hyps[10]],
    )
    p_I_X_E, _ = apn("eqcomd", {"ph": E, "A": X, "B": I}, [p_iftrue])
    p_I_X_P, _ = apn(
        "adantr", {"ph": E, "ps": eq(I, X), "ch": ph}, [p_I_X_E]
    )
    p_pack0 = transport_package(
        P,
        pack0_I,
        pack0_X,
        I,
        X,
        fun0,
        C,
        m,
        p_P_pack0I,
        p_I_X_P,
    )

    p_Q_ps, _ = apn("simpr", {"ph": E, "ps": ps})
    p_Q_pack1I, _ = apn(
        "syl",
        {"ph": Q, "ps": ps, "ch": pack1_I},
        [p_Q_ps, target_hyps[11]],
    )
    p_tc_I_X_imp, _ = apn("tceq", {"A": I, "B": X})
    p_tc_I_X_E, _ = apn(
        "syl",
        {"ph": E, "ps": eq(I, X), "ch": eq(tcI, tcX)},
        [p_I_X_E, p_tc_I_X_imp],
    )
    p_tc_I_X_Q, _ = apn(
        "adantr", {"ph": E, "ps": eq(tcI, tcX), "ch": ps}, [p_tc_I_X_E]
    )
    p_pack1 = transport_package(
        Q,
        pack1_I,
        pack1_X,
        tcI,
        tcX,
        fun1,
        tcC,
        k,
        p_Q_pack1I,
        p_tc_I_X_Q,
    )

    p_R_ch, _ = apn("simpr", {"ph": E, "ps": ch})
    p_growth, _ = apn(
        "syl",
        {"ph": R, "ps": ch, "ch": growth},
        [p_R_ch, target_hyps[12]],
    )

    # Replace only the donor's twelve essential leaves and four syntax leaves.
    premise_map = {
        f"{SOURCE}.1": target_hyps[1],
        f"{SOURCE}.2": target_hyps[2],
        f"{SOURCE}.3": target_hyps[3],
        f"{SOURCE}.4": target_hyps[4],
        f"{SOURCE}.5": target_hyps[5],
        f"{SOURCE}.6": target_hyps[6],
        f"{SOURCE}.7": p_X_hw,
        f"{SOURCE}.8": p_X_fixed,
        f"{SOURCE}.9": target_hyps[9],
        f"{SOURCE}.10": p_pack0,
        f"{SOURCE}.11": p_pack1,
        f"{SOURCE}.12": p_growth,
    }
    syntax_subst = {"I": X, "ph": P, "ps": Q, "ch": R}
    missing_dependencies = sorted(
        {
            node.label
            for node in donor_nodes
            if node.label not in premise_map
            and not (
                node.label in floating_var
                and floating_var[node.label][1] in syntax_subst
            )
            and node.label not in db.stmts
        }
    )
    if missing_dependencies:
        raise KeyError(
            "donor dependencies not retained in endpoint: "
            + ", ".join(missing_dependencies)
        )
    for node in donor_nodes:
        if node.label in premise_map:
            node.replacement = premise_map[node.label]
        elif node.label in floating_var and floating_var[node.label][1] in syntax_subst:
            typecode, variable = floating_var[node.label]
            node.replacement = syntax_node((typecode,) + syntax_subst[variable])
        else:
            if node.args:
                node.args = tuple(arg.replacement for arg in node.args)  # type: ignore[arg-type]
            node.replacement = node
    instantiated_source = donor_root.replacement
    assert instantiated_source is not None

    # Pure propositional reshaping of the donor conclusion to the public form.
    antecedent_pair = conj(E, gamma)
    p_ag_E, _ = apn("simpl", {"ph": E, "ps": gamma})
    p_ag_gamma, _ = apn("simpr", {"ph": E, "ps": gamma})
    p_gamma_ph, _ = apn("simpl", {"ph": ph, "ps": conj(ps, ch)})
    p_gamma_psch, _ = apn("simpr", {"ph": ph, "ps": conj(ps, ch)})
    p_psch_ps, _ = apn("simpl", {"ph": ps, "ps": ch})
    p_psch_ch, _ = apn("simpr", {"ph": ps, "ps": ch})
    p_ag_ph, _ = apn(
        "syl",
        {"ph": antecedent_pair, "ps": gamma, "ch": ph},
        [p_ag_gamma, p_gamma_ph],
    )
    p_ag_psch, _ = apn(
        "syl",
        {"ph": antecedent_pair, "ps": gamma, "ch": conj(ps, ch)},
        [p_ag_gamma, p_gamma_psch],
    )
    p_ag_ps, _ = apn(
        "syl",
        {"ph": antecedent_pair, "ps": conj(ps, ch), "ch": ps},
        [p_ag_psch, p_psch_ps],
    )
    p_ag_ch, _ = apn(
        "syl",
        {"ph": antecedent_pair, "ps": conj(ps, ch), "ch": ch},
        [p_ag_psch, p_psch_ch],
    )
    p_ag_P, _ = apn(
        "jca", {"ph": antecedent_pair, "ps": E, "ch": ph}, [p_ag_E, p_ag_ph]
    )
    p_ag_Q, _ = apn(
        "jca", {"ph": antecedent_pair, "ps": E, "ch": ps}, [p_ag_E, p_ag_ps]
    )
    p_ag_R, _ = apn(
        "jca", {"ph": antecedent_pair, "ps": E, "ch": ch}, [p_ag_E, p_ag_ch]
    )
    p_ag_QR, _ = apn(
        "jca",
        {"ph": antecedent_pair, "ps": Q, "ch": R},
        [p_ag_Q, p_ag_R],
    )
    source_antecedent = conj(P, conj(Q, R))
    p_ag_source, _ = apn(
        "jca",
        {"ph": antecedent_pair, "ps": P, "ch": conj(Q, R)},
        [p_ag_P, p_ag_QR],
    )
    p_curried, _ = apn(
        "ex",
        {"ph": E, "ps": gamma, "ch": source_antecedent},
        [p_ag_source],
    )
    final_root, final_expr = apn(
        "syl6",
        {"ph": E, "ps": gamma, "ch": source_antecedent, "th": bottom},
        [p_curried, instantiated_source],
    )
    assert final_expr == ("|-",) + target_body

    proof, dag_nodes, saved_nodes = compressed(db, TARGET, final_root)
    PROOF.write_text(proof + "\n", encoding="utf-8", newline="\n")
    pre_text = PRE.read_text(encoding="utf-8")
    start = pre_text.index(TARGET + " $p")
    hole = pre_text.index("$= ? $.", start)
    out_text = pre_text[:hole] + "$= " + proof + " $." + pre_text[hole + len("$= ? $.") :]
    OUT.write_text(out_text, encoding="utf-8", newline="\n")

    # First static verification is in-process and exercises the generated proof.
    mpb.load(OUT, verify=True, allow_incomplete=False)

    base_text = BASE.read_text(encoding="utf-8")
    base_start = base_text.index(TARGET + " $p")
    base_proof_start = base_text.index("$=", base_start)
    base_proof_end = base_text.index("$.", base_proof_start) + 2
    out_start = out_text.index(TARGET + " $p")
    out_proof_start = out_text.index("$=", out_start)
    out_proof_end = out_text.index("$.", out_proof_start) + 2
    assert base_text[:base_proof_start] == out_text[:out_proof_start]
    assert base_text[base_proof_end:] == out_text[out_proof_end:]

    report = {
        "frozen": True,
        "base": str(BASE),
        "base_sha256": sha256(BASE),
        "base_bytes": BASE.stat().st_size,
        "output": str(OUT),
        "output_sha256": sha256(OUT),
        "output_bytes": OUT.stat().st_size,
        "byte_delta": OUT.stat().st_size - BASE.stat().st_size,
        "changed_assertions": [TARGET],
        "nonproof_prefix_identical": True,
        "nonproof_suffix_identical": True,
        "old_proof_bytes": base_proof_end - base_proof_start,
        "new_proof_bytes": out_proof_end - out_proof_start,
        "proof_byte_delta": (out_proof_end - out_proof_start)
        - (base_proof_end - base_proof_start),
        "old_proof_region_sha256": sha256_text(
            base_text[base_proof_start:base_proof_end]
        ),
        "new_proof_region_sha256": sha256_text(
            out_text[out_proof_start:out_proof_end]
        ),
        "proof_artifact": str(PROOF),
        "proof_artifact_sha256": sha256(PROOF),
        "builder": str(Path(__file__).resolve()),
        "builder_sha256": sha256(Path(__file__).resolve()),
        "donor_unique_nodes": donor_node_count,
        "shallow_expansions": shallow_expansions,
        "output_dag_nodes": dag_nodes,
        "output_saved_nodes": saved_nodes,
        "method": "single shallow conditional-class instantiation of donor DAG",
    }
    REPORT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    DELTA.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
