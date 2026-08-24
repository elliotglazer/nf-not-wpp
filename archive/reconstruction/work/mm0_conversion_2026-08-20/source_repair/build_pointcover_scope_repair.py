#!/usr/bin/env python3
"""Repair the inactive q-membership hypothesis in cfbhnpw13pointcoverndv.

This operates only on the isolated MM0 endpoint audit copy.  It keeps the
assertion fixed and rebuilds the proof with a constant-size weak-deduction
step.  The false branch uses a canonical source point made from the default
normalized code, so no hypothesis from the earlier code-point scope is
referenced.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
DEFAULT_INPUT = HERE / "endpoint_after_fdminvalp.mm"
INPUT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else DEFAULT_INPUT
OUTPUT = (
    Path(sys.argv[2]).resolve()
    if len(sys.argv) > 2
    else HERE / "endpoint_after_fdminvalp_pointcover.mm"
)
PRE = OUTPUT.with_name(OUTPUT.stem + "_pre.mm")
REPORT = OUTPUT.with_suffix(".audit.json")
BUILDER = WORKSPACE / "formalization_continue/reconstruct/mmproof_builder_current.py"
VERIFY = WORKSPACE / "work/formalization_continue/root_integration/local_mm_verify_compressed.py"
STRICT_VERIFY = (
    WORKSPACE
    / "work/mm0_conversion_2026-08-20/strict_scope/"
    "local_mm_verify_compressed_strict_scope.py"
)
TARGET = "cfbhnpw13pointcoverndv"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def theorem_pattern(label: str) -> re.Pattern[str]:
    return re.compile(
        r"(" + re.escape(label) + r"\s+\$p\s+.*?\$=)\s*.*?\s*\$\.",
        re.S,
    )


def hole_proof(text: str, label: str) -> str:
    text, count = theorem_pattern(label).subn(
        lambda match: match.group(1) + " ? $.", text, count=1
    )
    if count != 1:
        raise RuntimeError(f"could not hole {label}: {count}")
    return text


def install_proof(text: str, label: str, proof: str) -> str:
    marker = re.compile(
        r"(" + re.escape(label) + r"\s+\$p\s+.*?\$=)\s*\?\s*\$\.",
        re.S,
    )
    text, count = marker.subn(
        lambda match: match.group(1) + " " + proof + " $.", text, count=1
    )
    if count != 1:
        raise RuntimeError(f"could not install {label}: {count}")
    return text


def flat(*parts):
    out: list[str] = []
    for part in parts:
        out.extend(part if isinstance(part, tuple) else (part,))
    return tuple(out)


def par(*parts):
    return flat("(", *parts, ")")


def mem(left, right):
    return flat(left, "e.", right)


def eq(left, right):
    return flat(left, "=", right)


def iff(left, right):
    return par(left, "<->", right)


def imp(left, right):
    return par(left, "->", right)


def conj(left, right):
    return par(left, "/\\", right)


def neg(formula):
    return flat("-.", formula)


def cif(formula, yes, no):
    return flat("if", "(", formula, ",", yes, ",", no, ")")


def compress(db, label: str, proof: list[str]) -> str:
    mandatory = list(db.stmts[label].mand_hyps)
    extras: list[str] = []
    for token in proof:
        if token not in mandatory and token not in extras:
            extras.append(token)
    table = mandatory + extras

    def encode(number: int) -> str:
        quotient, final = divmod(number - 1, 20)
        prefix: list[str] = []
        while quotient:
            quotient, digit = divmod(quotient - 1, 5)
            prefix.append(chr(ord("U") + digit))
        return "".join(reversed(prefix)) + chr(ord("A") + final)

    return "( " + " ".join(extras) + " ) " + "".join(
        encode(table.index(token) + 1) for token in proof
    )


def build_proof():
    builder_module = load_module("pointcover_scope_builder", BUILDER)
    db = builder_module.load(PRE, verify=False, allow_incomplete=True)
    builder = builder_module.Builder(db)

    def ap(label, subst=None, essentials=()):
        return builder.apply(label, subst or {}, list(essentials))

    V = ("_V",)
    X = ("X",)
    q = ("q",)
    u = ("u",)
    WPP = ("WPP",)
    EMPTY = ("(/)",)

    PX = flat("~P", X)
    H0 = flat("HNOrd", PX)
    S1 = flat("~P1", H0)
    S2 = flat("~P1", S1)
    S3 = flat("~P1", S2)
    P3PX = flat("~P1", "~P1", "~P1", PX)
    HNOX = flat("HNOrd", X)
    Y = flat("~P", "~P", HNOX)
    AMBIENT = par(P3PX, "u.", Y)
    J = par(
        flat("HNSIQuoMap", "~P1", "~P1", PX),
        "o.",
        par(
            flat("SI", "HNSIQuoMap", "~P1", PX),
            "o.",
            flat("SI", "SI", "HNSIQuoMap", PX),
        ),
    )
    source_map = par(flat("HNQInc", "(", P3PX, ",", AMBIENT, ")"), "o.", J)
    target_range = flat("ran", "HNQInc", "(", Y, ",", AMBIENT, ")")

    def point(z):
        return mem(par(source_map, "`", z), target_range)

    def wq(z):
        return imp(WPP, point(z))

    def quotient(code):
        return flat("[", code, "]", "HWNIso", PX)

    def rep(z, code):
        return eq(flat("U.", "U.", "U.", z), quotient(code))

    def rex(z):
        return flat("E.", u, "e.", flat("HWCN", PX), rep(z, u))

    hp = [(f"{TARGET}.{index}",) for index in range(1, 3)]
    source_hyp = mem(q, S3)

    # Build a fixed normalized code and its quotient, then lift it through
    # three singleton carriers to obtain a source point q0 in S3.
    XP0 = par(EMPTY, "X.", EMPTY)
    KQ = flat("KQRel", "<_[fin]")
    R0 = par(KQ, "i^i", XP0)
    u0 = flat("<.", R0, ",", EMPTY, ">.")
    u0_mem, _ = ap("hncodecmpdefaultcnndv", {"X": X, "A": PX})
    px_set, _ = ap("pwex", {"A": X}, [hp[0]])
    h0 = quotient(u0)
    h0_mem_rule, _ = ap(
        "hwnisoclasselhnordcl", {"A": PX, "B": u0}, [px_set]
    )
    h0_mem, _ = ap(
        "ax-mp", {"ph": mem(u0, flat("HWCN", PX)), "ps": mem(h0, H0)},
        [u0_mem, h0_mem_rule]
    )
    h0_set_rule, _ = ap("elex", {"A": h0, "B": H0})
    h0_set, _ = ap(
        "ax-mp", {"ph": mem(h0, H0), "ps": mem(h0, V)},
        [h0_mem, h0_set_rule]
    )

    q1 = flat("{", h0, "}")
    q2 = flat("{", q1, "}")
    q0 = flat("{", q2, "}")
    q1_bi, _ = ap("snelpw1", {"A": h0, "B": H0})
    q1_mem, _ = ap(
        "mpbir", {"ph": mem(q1, S1), "ps": mem(h0, H0)},
        [h0_mem, q1_bi]
    )
    q2_bi, _ = ap("snelpw1", {"A": q1, "B": S1})
    q2_mem, _ = ap(
        "mpbir", {"ph": mem(q2, S2), "ps": mem(q1, S1)},
        [q1_mem, q2_bi]
    )
    q0_bi, _ = ap("snelpw1", {"A": q2, "B": S2})
    q0_mem, _ = ap(
        "mpbir", {"ph": mem(q0, S3), "ps": mem(q2, S2)},
        [q2_mem, q0_bi]
    )

    # Conditionalize q on the missing source-membership hypothesis.  Both
    # branches are in S3, so the earlier code-point theorem is applicable
    # with only hypotheses active in the present theorem.
    IQ = cif(source_hyp, q, q0)
    TAUT = eq(EMPTY, EMPTY)
    taut, _ = ap("eqid", {"A": EMPTY})
    true_source, _ = ap("simpr", {"ph": TAUT, "ps": source_hyp})
    false_source, _ = ap(
        "a1i", {"ph": mem(q0, S3), "ps": conj(TAUT, neg(source_hyp))},
        [q0_mem]
    )
    if_source_rule, _ = ap(
        "ifclda", {"ph": TAUT, "ps": source_hyp,
                    "A": q, "B": q0, "C": S3},
        [true_source, false_source]
    )
    iq_mem, _ = ap(
        "ax-mp", {"ph": TAUT, "ps": mem(IQ, S3)},
        [taut, if_source_rule]
    )

    # The endpoint slice no longer contains the intermediate
    # cfbhnpw13codepointimndv assertion, so rebuild its small weak-deduction
    # step from the retained class-code theorem instead of restoring a dead
    # assertion to the slice.
    PHIC = mem(u, flat("HWCN", PX))
    IU = cif(PHIC, u, u0)
    true_code, _ = ap("simpr", {"ph": TAUT, "ps": PHIC})
    false_code, _ = ap(
        "a1i", {"ph": mem(u0, flat("HWCN", PX)),
                 "ps": conj(TAUT, neg(PHIC))},
        [u0_mem]
    )
    if_code_rule, _ = ap(
        "ifclda", {"ph": TAUT, "ps": PHIC,
                    "A": u, "B": u0, "C": flat("HWCN", PX)},
        [true_code, false_code]
    )
    if_code, _ = ap(
        "ax-mp", {"ph": TAUT, "ps": mem(IU, flat("HWCN", PX))},
        [taut, if_code_rule]
    )
    # Internalize the representative equality at the class-valued IQ.  The
    # retained qrep theorem is set-variable-only, so repeat its shallow
    # class-native construction using the retained generic code-point theorem.
    hval = quotient(IU)
    r1 = flat("{", hval, "}")
    r2 = flat("{", r1, "}")
    r0 = flat("{", r2, "}")
    PHIR = rep(IQ, IU)
    JQ = cif(PHIR, IQ, r0)

    hval_mem_rule, _ = ap(
        "hwnisoclasselhnordcl", {"A": PX, "B": IU}, [px_set]
    )
    hval_mem, _ = ap(
        "ax-mp", {"ph": mem(IU, flat("HWCN", PX)),
                   "ps": mem(hval, H0)},
        [if_code, hval_mem_rule]
    )
    hval_set_rule, _ = ap("elex", {"A": hval, "B": H0})
    hval_set, _ = ap(
        "ax-mp", {"ph": mem(hval, H0), "ps": mem(hval, V)},
        [hval_mem, hval_set_rule]
    )
    r1_bi, _ = ap("snelpw1", {"A": hval, "B": H0})
    r1_mem, _ = ap(
        "mpbir", {"ph": mem(r1, S1), "ps": mem(hval, H0)},
        [hval_mem, r1_bi]
    )
    r2_bi, _ = ap("snelpw1", {"A": r1, "B": S1})
    r2_mem, _ = ap(
        "mpbir", {"ph": mem(r2, S2), "ps": mem(r1, S1)},
        [r1_mem, r2_bi]
    )
    r0_bi, _ = ap("snelpw1", {"A": r2, "B": S2})
    r0_mem, _ = ap(
        "mpbir", {"ph": mem(r0, S3), "ps": mem(r2, S2)},
        [r2_mem, r0_bi]
    )
    r1_set, _ = ap("snex", {"A": hval}, [hval_set])
    r2_set, _ = ap("snex", {"A": r1}, [r1_set])
    un3, _ = ap("unisn", {"A": r2}, [r2_set])
    uun3, _ = ap("unieqi", {"A": flat("U.", r0), "B": r2}, [un3])
    un2, _ = ap("unisn", {"A": r1}, [r1_set])
    uu_mid, _ = ap(
        "eqtri", {"A": flat("U.", "U.", r0), "B": flat("U.", r2),
                  "C": r1},
        [uun3, un2]
    )
    uuu_mid, _ = ap(
        "unieqi", {"A": flat("U.", "U.", r0), "B": r1}, [uu_mid]
    )
    un1, _ = ap("unisn", {"A": hval}, [hval_set])
    r0_rep, _ = ap(
        "eqtri", {"A": flat("U.", "U.", "U.", r0),
                  "B": flat("U.", r1), "C": hval},
        [uuu_mid, un1]
    )

    both_rep_source, _ = ap(
        "pm3.2i", {"ph": mem(IQ, S3), "ps": mem(r0, S3)},
        [iq_mem, r0_mem]
    )
    jq_mem_rule, _ = ap("ifcl", {"ph": PHIR, "A": IQ, "B": r0, "C": S3})
    jq_mem, _ = ap(
        "ax-mp", {"ph": conj(mem(IQ, S3), mem(r0, S3)),
                   "ps": mem(JQ, S3)},
        [both_rep_source, jq_mem_rule]
    )
    if_true, _ = ap("iftrue", {"ph": PHIR, "A": IQ, "B": r0})
    t1, _ = ap("unieqd", {"ph": PHIR, "A": JQ, "B": IQ}, [if_true])
    t2, _ = ap(
        "unieqd", {"ph": PHIR, "A": flat("U.", JQ),
                    "B": flat("U.", IQ)},
        [t1]
    )
    t3, _ = ap(
        "unieqd", {"ph": PHIR, "A": flat("U.", "U.", JQ),
                    "B": flat("U.", "U.", IQ)},
        [t2]
    )
    rep_id, _ = ap("id", {"ph": PHIR})
    true_rep, _ = ap(
        "eqtrd", {"ph": PHIR, "A": flat("U.", "U.", "U.", JQ),
                  "B": flat("U.", "U.", "U.", IQ), "C": hval},
        [t3, rep_id]
    )
    not_rep = neg(PHIR)
    if_false, _ = ap("iffalse", {"ph": PHIR, "A": IQ, "B": r0})
    f1, _ = ap("unieqd", {"ph": not_rep, "A": JQ, "B": r0}, [if_false])
    f2, _ = ap(
        "unieqd", {"ph": not_rep, "A": flat("U.", JQ),
                    "B": flat("U.", r0)},
        [f1]
    )
    f3, _ = ap(
        "unieqd", {"ph": not_rep, "A": flat("U.", "U.", JQ),
                    "B": flat("U.", "U.", r0)},
        [f2]
    )
    r0_rep_false, _ = ap("a1i", {"ph": rep(r0, IU), "ps": not_rep}, [r0_rep])
    false_rep, _ = ap(
        "eqtrd", {"ph": not_rep, "A": flat("U.", "U.", "U.", JQ),
                  "B": flat("U.", "U.", "U.", r0), "C": hval},
        [f3, r0_rep_false]
    )
    jq_rep, _ = ap("pm2.61i", {"ph": PHIR, "ps": rep(JQ, IU)},
                   [true_rep, false_rep])
    jq_point, _ = ap(
        "cfbhnpw13genericcodepointcoverndv", {"X": X, "C": IU, "Q": JQ},
        [hp[0], if_code, jq_mem, jq_rep, hp[1]]
    )
    IQEQ = eq(IQ, JQ)
    iqeq_id, _ = ap("id", {"ph": IQEQ})
    jq_value_eq, _ = ap(
        "fveq2d", {"ph": IQEQ, "F": source_map, "A": IQ, "B": JQ},
        [iqeq_id]
    )
    jq_cover_bi, _ = ap(
        "eleq1d", {"ph": IQEQ, "A": par(source_map, "`", IQ),
                    "B": par(source_map, "`", JQ), "C": target_range},
        [jq_value_eq]
    )
    jq_wq_bi, _ = ap(
        "imbi2d", {"ph": IQEQ, "ps": point(IQ), "ch": point(JQ),
                   "th": WPP},
        [jq_cover_bi]
    )
    if_rep_point, _ = ap(
        "dedth", {"A": IQ, "B": r0, "ph": PHIR,
                  "ps": wq(IQ), "ch": wq(JQ)},
        [jq_wq_bi, jq_point]
    )
    UEQ = eq(u, IU)
    quotient_eq, _ = ap(
        "eceq1", {"A": u, "B": IU, "C": flat("HWNIso", PX)}
    )
    code_rep_bi, _ = ap(
        "eqeq2d", {"ph": UEQ, "A": quotient(u), "B": quotient(IU),
                    "C": flat("U.", "U.", "U.", IQ)},
        [quotient_eq]
    )
    code_imp_bi, _ = ap(
        "imbi1d", {"ph": UEQ, "ps": rep(IQ, u), "ch": rep(IQ, IU),
                    "th": wq(IQ)},
        [code_rep_bi]
    )
    iq_code_point, _ = ap(
        "dedth", {"A": u, "B": u0, "ph": PHIC,
                   "ps": imp(rep(IQ, u), wq(IQ)),
                   "ch": imp(rep(IQ, IU), wq(IQ))},
        [code_imp_bi, if_rep_point]
    )
    iq_rex_point, _ = ap(
        "rexlimiv", {"x": u, "A": flat("HWCN", PX),
                      "ph": rep(IQ, u), "ps": wq(IQ)},
        [iq_code_point]
    )

    # Equality q = IQ transports both the representative existential and the
    # coverage conclusion.  Weak deduction then turns source_hyp into the
    # required antecedent without referring to an out-of-scope $e label.
    QEQ = eq(q, IQ)
    qeq_id, _ = ap("id", {"ph": QEQ})
    u1eq, _ = ap("unieqd", {"ph": QEQ, "A": q, "B": IQ}, [qeq_id])
    u2eq, _ = ap(
        "unieqd", {"ph": QEQ, "A": flat("U.", q), "B": flat("U.", IQ)},
        [u1eq]
    )
    u3eq, _ = ap(
        "unieqd", {"ph": QEQ, "A": flat("U.", "U.", q),
                    "B": flat("U.", "U.", IQ)},
        [u2eq]
    )
    rep_bi, _ = ap(
        "eqeq1d", {"ph": QEQ, "A": flat("U.", "U.", "U.", q),
                    "B": flat("U.", "U.", "U.", IQ), "C": quotient(u)},
        [u3eq]
    )
    rex_bi, _ = ap(
        "rexbidv", {"x": u, "A": flat("HWCN", PX), "ph": QEQ,
                     "ps": rep(q, u), "ch": rep(IQ, u)},
        [rep_bi]
    )
    source_value_eq, _ = ap(
        "fveq2d", {"ph": QEQ, "F": source_map, "A": q, "B": IQ},
        [qeq_id]
    )
    cover_bi, _ = ap(
        "eleq1d", {"ph": QEQ, "A": par(source_map, "`", q),
                    "B": par(source_map, "`", IQ), "C": target_range},
        [source_value_eq]
    )
    wq_bi, _ = ap(
        "imbi2d", {"ph": QEQ, "ps": point(q), "ch": point(IQ), "th": WPP},
        [cover_bi]
    )
    rex_point_bi, _ = ap(
        "imbi12d", {"ph": QEQ, "ps": rex(q), "ch": rex(IQ),
                     "th": wq(q), "ta": wq(IQ)},
        [rex_bi, wq_bi]
    )
    source_to_rex_point, _ = ap(
        "dedth", {"A": q, "B": q0, "ph": source_hyp,
                   "ps": imp(rex(q), wq(q)),
                   "ch": imp(rex(IQ), wq(IQ))},
        [rex_point_bi, iq_rex_point]
    )

    # The original Hartogs representative construction is already in
    # deduction form from source_hyp and therefore needs no scoped $e label.
    u1 = flat("U.", q)
    u2 = flat("U.", u1)
    h = flat("U.", u2)
    d1, _ = ap("pw1argclcl", {"Q": q, "D": S2})
    d1m, _ = ap(
        "simpld", {"ph": source_hyp, "ps": mem(u1, S2),
                    "ch": eq(q, flat("{", u1, "}"))},
        [d1]
    )
    d2rule, _ = ap("pw1argclcl", {"Q": u1, "D": S1})
    d2, _ = ap(
        "syl", {"ph": source_hyp, "ps": mem(u1, S2),
                 "ch": conj(mem(u2, S1), eq(u1, flat("{", u2, "}")))},
        [d1m, d2rule]
    )
    d2m, _ = ap(
        "simpld", {"ph": source_hyp, "ps": mem(u2, S1),
                    "ch": eq(u1, flat("{", u2, "}"))},
        [d2]
    )
    d3rule, _ = ap("pw1argclcl", {"Q": u2, "D": H0})
    d3, _ = ap(
        "syl", {"ph": source_hyp, "ps": mem(u2, S1),
                 "ch": conj(mem(h, H0), eq(u2, flat("{", h, "}")))},
        [d2m, d3rule]
    )
    hmem, _ = ap(
        "simpld", {"ph": source_hyp, "ps": mem(h, H0),
                    "ch": eq(u2, flat("{", h, "}"))},
        [d3]
    )
    hset_rule, _ = ap("elex", {"A": h, "B": H0})
    hset, _ = ap(
        "syl", {"ph": source_hyp, "ps": mem(h, H0), "ch": mem(h, V)},
        [hmem, hset_rule]
    )
    elhn, _ = ap("elhnordclndv", {"X": h, "A": PX, "u": u})
    elhn_at_q, _ = ap(
        "syl", {"ph": source_hyp, "ps": mem(h, V),
                 "ch": iff(mem(h, H0), rex(q))},
        [hset, elhn]
    )
    rex_from_q, _ = ap(
        "mpbid", {"ph": source_hyp, "ps": mem(h, H0), "ch": rex(q)},
        [hmem, elhn_at_q]
    )
    final_proof, final_expr = ap(
        "mpd", {"ph": source_hyp, "ps": rex(q), "ch": wq(q)},
        [rex_from_q, source_to_rex_point]
    )
    if tuple(final_expr) != db.stmts[TARGET].expr:
        raise RuntimeError((final_expr, db.stmts[TARGET].expr))
    return db, list(final_proof)


def run_local_checker(path: Path) -> tuple[int, int]:
    module = load_module("pointcover_scope_checker", VERIFY)
    checker = module.MM(WORKSPACE / "work/formalization_continue")
    checker.process(path)
    if checker.trusted:
        raise RuntimeError(f"unexpected trusted proofs: {checker.trusted!r}")
    return len(checker.verified), len(checker.trusted)


def run_strict_checker(path: Path) -> dict[str, object]:
    module = load_module("pointcover_strict_checker", STRICT_VERIFY)
    checker = module.MM(path.parent)
    checker.process(path)
    return {
        "status": (
            "PASS" if not checker.scope_errors
            else "FAIL_INACTIVE_HYPOTHESIS_SCOPE"
        ),
        "rejected_proof_count": len(checker.rejected_proofs),
        "inactive_hypothesis_reference_count": len(checker.scope_errors),
        "inactive_hypothesis_references": list(checker.scope_errors),
    }


def main() -> None:
    source = INPUT.read_text(encoding="utf-8")
    PRE.write_text(hole_proof(source, TARGET), encoding="utf-8", newline="\n")
    db, proof = build_proof()
    output = install_proof(PRE.read_text(encoding="utf-8"), TARGET,
                           compress(db, TARGET, proof))
    OUTPUT.write_text(output, encoding="utf-8", newline="\n")
    verified, trusted = run_local_checker(OUTPUT)
    strict = run_strict_checker(OUTPUT)
    report = {
        "source": str(INPUT),
        "source_sha256": sha256(INPUT),
        "output": str(OUTPUT),
        "output_sha256": sha256(OUTPUT),
        "target": TARGET,
        "target_assertion_unchanged": True,
        "new_statements": 0,
        "verified_proofs": verified,
        "trusted_proofs": trusted,
        "strict_status": strict.get("status"),
        "strict_rejected_proof_count": strict.get("rejected_proof_count"),
        "strict_inactive_hypothesis_reference_count": strict.get(
            "inactive_hypothesis_reference_count"
        ),
        "strict_inactive_f_reference_count": sum(
            1
            for item in strict.get("inactive_hypothesis_references", [])
            if item.get("referenced_kind") == "$f"
        ),
        "published_file_modified": False,
    }
    REPORT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
