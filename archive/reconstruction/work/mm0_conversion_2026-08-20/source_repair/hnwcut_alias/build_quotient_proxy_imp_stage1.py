#!/usr/bin/env python3
"""Build a small REQ-deduction quotient proxy for the HNWCut scope repair.

This is a manual proof composition.  It does not recursively expand any proof.
The sole essential hypothesis is A set; the comparator proxy equality is carried
inside the theorem antecedent.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MPB = ROOT / "formalization_continue/reconstruct/mmproof_builder_current.py"
BASE = ROOT / "work/mm0_conversion_2026-08-20/integration/endpoint_after_df_lnwmap_wppstop.mm"
PRE = HERE / "quotient_proxy_imp_stage1_pre.mm"
OUT = HERE / "quotient_proxy_imp_stage1_checkpoint.mm"
MARKER = "$( Linear replay source: C:/Users/glaze/Documents/Codex/2026-08-16/study-the-contents-of-this-and/work/formalization_continue/hnord_wellorder/hnwcut_ambient_strict_segment_isom_alias_checkpoint.mm $)"
LABEL = "hncodecmpquotbrproxyimpndv"

spec = importlib.util.spec_from_file_location("hnwcut_qproxy_imp_builder", MPB)
assert spec is not None and spec.loader is not None
mpb = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mpb
spec.loader.exec_module(mpb)


BLOCK = r"""$( Deduction-form exact quotient relation.  The comparator proxy
   equality is an antecedent, so later class substitutions do not collide with
   the quotient constructor's C,R distinct-variable requirement. $)
${
  $d A r $.  $d A u $.  $d A v $.
  hncodecmpquotbrproxyimpndv.1 $e |- A e. _V $.
  hncodecmpquotbrproxyimpndv $p |- (
    ( r = HNCodeCmpSet A /\
      ( u e. HWCN A /\ v e. HWCN A ) ) ->
    ( [ u ] HWNIso A LNQOrd ( r , HWCN A ) [ v ] HWNIso A
      <-> u HNCodeCmpSet A v ) ) $= ? $.
$}

"""


def flat(*parts):
    out = []
    for part in parts:
        out.extend(part if isinstance(part, tuple) else (part,))
    return tuple(out)


def mem(a, c): return flat(a, "e.", c)
def eq(a, c): return flat(a, "=", c)
def conj(a, c): return flat("(", a, "/\\", c, ")")
def imp(a, c): return flat("(", a, "->", c, ")")
def bi(a, c): return flat("(", a, "<->", c, ")")
def br(a, r, c): return flat(a, r, c)
def par(*parts): return flat("(", *parts, ")")
def qs(a, r): return flat("[", a, "]", r)


def ap(builder, label, subst=None, essentials=()):
    return builder.apply(label, subst or {}, list(essentials))


def compressed(db, label, proof):
    mandatory = list(db.stmts[label].mand_hyps)
    extra = []
    for token in proof:
        if token not in mandatory and token not in extra:
            extra.append(token)
    table = mandatory + extra

    def enc(n):
        q, last = divmod(n - 1, 20)
        prefix = []
        while q:
            q, digit = divmod(q - 1, 5)
            prefix.append(chr(ord("U") + digit))
        return "".join(reversed(prefix)) + chr(ord("A") + last)

    return "( " + " ".join(extra) + " ) " + "".join(
        enc(table.index(token) + 1) for token in proof
    )


def make_pre() -> None:
    text = BASE.read_text(encoding="utf-8")
    if MARKER not in text:
        raise RuntimeError("HNWCut alias marker not found")
    PRE.write_text(text.replace(MARKER, BLOCK + MARKER, 1), encoding="utf-8", newline="\n")


def main() -> None:
    make_pre()
    db = mpb.load(PRE, verify=False, allow_incomplete=True)
    b = mpb.Builder(db)

    A = ("A",); r = ("r",); u = ("u",); v = ("v",)
    V = ("_V",)
    C = flat("HNCodeCmpSet", A)
    H = flat("HWCN", A)
    ISO = flat("HWNIso", A)
    L = flat("LNQOrd", "(", r, ",", H, ")")
    ASET = mem(A, V)
    REQ = eq(r, C)
    UM = mem(u, H); VM = mem(v, H); G = conj(UM, VM)
    CTX = conj(REQ, G)

    h_aset = ap(b, LABEL + ".1")[0]
    c_req = ap(b, "simpl", {"ph": REQ, "ps": G})[0]
    c_g = ap(b, "simpr", {"ph": REQ, "ps": G})[0]
    c_aset = ap(b, "a1i", {"ph": ASET, "ps": CTX}, (h_aset,))[0]
    c_um = ap(
        b, "syl", {"ph": CTX, "ps": G, "ch": UM},
        (c_g, ap(b, "simpl", {"ph": UM, "ps": VM})[0])
    )[0]
    c_vm = ap(
        b, "syl", {"ph": CTX, "ps": G, "ch": VM},
        (c_g, ap(b, "simpr", {"ph": UM, "ps": VM})[0])
    )[0]

    CSET = mem(C, V); HSET = mem(H, V); RSET = mem(r, V)
    c_cset = ap(
        b, "syl", {"ph": CTX, "ps": ASET, "ch": CSET},
        (c_aset, ap(b, "hncodecmpsetexg", {"A": A})[0])
    )[0]
    c_hset = ap(
        b, "syl", {"ph": CTX, "ps": ASET, "ch": HSET},
        (c_aset, ap(b, "hwcnexg", {"A": A})[0])
    )[0]
    c_rset_bi = ap(
        b, "eleq1d", {"ph": CTX, "A": r, "B": C, "C": V}, (c_req,)
    )[0]
    c_rset = ap(
        b, "mpbird", {"ph": CTX, "ps": RSET, "ch": CSET},
        (c_cset, c_rset_bi)
    )[0]

    HXH = par(H, "X.", H)
    CREF = br(C, "Ref", H); RREF = br(r, "Ref", H)
    CTRANS = br(C, "Trans", H); RTRANS = br(r, "Trans", H)
    CSS = flat(C, "C_", HXH); RSS = flat(r, "C_", HXH)

    def cmp_fact(label, target):
        return ap(
            b, "syl", {"ph": CTX, "ps": ASET, "ch": target},
            (c_aset, ap(b, label, {"A": A})[0])
        )[0]

    c_cref = cmp_fact("hncodecmpsetrefndv", CREF)
    c_ctrans = cmp_fact("hncodecmpsettransndv", CTRANS)
    c_css = ap(b, "a1i", {"ph": CSS, "ps": CTX},
               (ap(b, "hncodecmpsetssxpndv", {"A": A})[0],))[0]

    def transport_property(cprop, rprop, proof, rel):
        equiv = ap(
            b, "breq1d", {"ph": CTX, "A": r, "B": C, "C": H, "R": rel},
            (c_req,)
        )[0]
        return ap(
            b, "mpbird", {"ph": CTX, "ps": rprop, "ch": cprop},
            (proof, equiv)
        )[0]

    c_rref = transport_property(CREF, RREF, c_cref, ("Ref",))
    c_rtrans = transport_property(CTRANS, RTRANS, c_ctrans, ("Trans",))
    c_ss_bi = ap(
        b, "sseq1d", {"ph": CTX, "A": r, "B": C, "C": HXH}, (c_req,)
    )[0]
    c_rss = ap(
        b, "mpbird", {"ph": CTX, "ps": RSS, "ch": CSS}, (c_css, c_ss_bi)
    )[0]

    RT = conj(RREF, RTRANS)
    PROPS = conj(RT, RSS)
    ENDS = conj(UM, VM)
    INNER = conj(PROPS, ENDS)
    ANT = conj(RSET, INNER)
    c_rt = ap(b, "jca", {"ph": CTX, "ps": RREF, "ch": RTRANS},
              (c_rref, c_rtrans))[0]
    c_props = ap(b, "jca", {"ph": CTX, "ps": RT, "ch": RSS},
                 (c_rt, c_rss))[0]
    c_ends = ap(b, "jca", {"ph": CTX, "ps": UM, "ch": VM},
                (c_um, c_vm))[0]
    c_inner = ap(b, "jca", {"ph": CTX, "ps": PROPS, "ch": ENDS},
                 (c_props, c_ends))[0]
    c_ant = ap(b, "jca", {"ph": CTX, "ps": RSET, "ch": INNER},
               (c_rset, c_inner))[0]

    KR = flat("LNKer", r); KC = flat("LNKer", C)
    QU = qs(u, KR); QV = qs(v, KR)
    BI_RAW = bi(br(QU, L, QV), br(u, r, v))
    c_raw = ap(
        b, "syl", {"ph": CTX, "ps": ANT, "ch": BI_RAW},
        (c_ant, ap(b, "brlnqordkern", {"R": r, "C": H, "X": u, "Y": v})[0])
    )[0]

    c_lnkereq = ap(
        b, "syl", {"ph": CTX, "ps": REQ, "ch": eq(KR, KC)},
        (c_req, ap(b, "lnkereq", {"R": r, "S": C})[0])
    )[0]
    c_kerc = ap(
        b, "syl", {"ph": CTX, "ps": ASET, "ch": eq(KC, ISO)},
        (c_aset, ap(b, "hncodecmplnkerndv", {"A": A})[0])
    )[0]
    c_ker = ap(
        b, "eqtrd", {"ph": CTX, "A": KR, "B": KC, "C": ISO},
        (c_lnkereq, c_kerc)
    )[0]
    c_qu = ap(
        b, "syl", {"ph": CTX, "ps": eq(KR, ISO), "ch": eq(QU, qs(u, ISO))},
        (c_ker, ap(b, "eceq2", {"A": KR, "B": ISO, "C": u})[0])
    )[0]
    c_qv = ap(
        b, "syl", {"ph": CTX, "ps": eq(KR, ISO), "ch": eq(QV, qs(v, ISO))},
        (c_ker, ap(b, "eceq2", {"A": KR, "B": ISO, "C": v})[0])
    )[0]
    LEFT_RAW = br(QU, L, QV)
    LEFT = br(qs(u, ISO), L, qs(v, ISO))
    c_left = ap(
        b, "breq12d",
        {"ph": CTX, "A": QU, "B": qs(u, ISO), "C": QV,
         "D": qs(v, ISO), "R": L},
        (c_qu, c_qv)
    )[0]
    c_left_rev = ap(
        b, "bicomd", {"ph": CTX, "ps": LEFT_RAW, "ch": LEFT}, (c_left,)
    )[0]
    RIGHT_RAW = br(u, r, v); RIGHT = br(u, C, v)
    c_right = ap(
        b, "breqd", {"ph": CTX, "A": r, "B": C, "C": u, "D": v}, (c_req,)
    )[0]
    c_right_rev = ap(
        b, "bicomd", {"ph": CTX, "ps": RIGHT_RAW, "ch": RIGHT}, (c_right,)
    )[0]
    c_final = ap(
        b, "3bitr4d",
        {"ph": CTX, "ps": LEFT_RAW, "ch": RIGHT_RAW,
         "th": LEFT, "ta": RIGHT},
        (c_raw, c_left_rev, c_right_rev)
    )[0]

    assert db.stmts[LABEL].expr == ("|-",) + imp(CTX, bi(LEFT, RIGHT))
    proof = compressed(db, LABEL, c_final)
    text = PRE.read_text(encoding="utf-8")
    needle = f"{LABEL} $p"
    start = text.index(needle)
    hole = text.index("$= ? $.", start)
    text = text[:hole] + "$= " + proof + " $." + text[hole + len("$= ? $."):]
    OUT.write_text(text, encoding="utf-8", newline="\n")
    mpb.load(OUT, verify=True, allow_incomplete=False)
    print(OUT)


if __name__ == "__main__":
    main()
