#!/usr/bin/env python3
"""Lift the verified REQ-deduction quotient proxy to class endpoints."""

from pathlib import Path
import importlib.util
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MPB = ROOT / "formalization_continue/reconstruct/mmproof_builder_current.py"
BASE = ROOT / "work/mm0_conversion_2026-08-20/source_repair/hnwcut_alias/quotient_proxy_imp_stage1_checkpoint.mm"
PRE = HERE / "quotient_proxy_imp_class_stage2_pre.mm"
OUT = HERE / "quotient_proxy_imp_class_stage2_checkpoint.mm"
MARKER = "$( Linear replay source: C:/Users/glaze/Documents/Codex/2026-08-16/study-the-contents-of-this-and/work/formalization_continue/hnord_wellorder/hnwcut_ambient_strict_segment_isom_alias_checkpoint.mm $)"
LABEL = "hncodecmpquotbrproxyimpclndv"

spec = importlib.util.spec_from_file_location("hnwcut_qproxy_imp_class_builder", MPB)
assert spec is not None and spec.loader is not None
mpb = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mpb
spec.loader.exec_module(mpb)

BLOCK = r"""$( Class-endpoint form of the deduction-form exact quotient relation. $)
${
  $d A r $.
  $d u A $.  $d u B $.  $d u C $.  $d u r $.  $d u v $.
  $d v A $.  $d v B $.  $d v C $.  $d v r $.
  hncodecmpquotbrproxyimpclndv.1 $e |- A e. _V $.
  hncodecmpquotbrproxyimpclndv $p |- (
    ( r = HNCodeCmpSet A /\
      ( B e. HWCN A /\ C e. HWCN A ) ) ->
    ( [ B ] HWNIso A LNQOrd ( r , HWCN A ) [ C ] HWNIso A
      <-> B HNCodeCmpSet A C ) ) $= ? $.
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


def main() -> None:
    text = BASE.read_text(encoding="utf-8")
    if MARKER not in text:
        raise RuntimeError("alias marker not found")
    PRE.write_text(text.replace(MARKER, BLOCK + MARKER, 1), encoding="utf-8", newline="\n")
    db = mpb.load(PRE, verify=False, allow_incomplete=True)
    b = mpb.Builder(db)

    A = ("A",); r = ("r",); u = ("u",); v = ("v",)
    B = ("B",); C = ("C",); V = ("_V",)
    H = flat("HWCN", A); CMP = flat("HNCodeCmpSet", A)
    ISO = flat("HWNIso", A); L = flat("LNQOrd", "(", r, ",", H, ")")
    REQ = eq(r, CMP)

    def formula(left, right):
        ends = conj(mem(left, H), mem(right, H))
        lhs = br(qs(left, ISO), L, qs(right, ISO))
        rhs = br(left, CMP, right)
        return imp(conj(REQ, ends), bi(lhs, rhs)), ends, lhs, rhs

    h_aset = ap(b, LABEL + ".1")[0]
    TUV, GUV, LUV, RUV = formula(u, v)
    TUC, GUC, LUC, RUC = formula(u, C)
    TBC, GBC, LBC, RBC = formula(B, C)
    p_base = ap(
        b, "hncodecmpquotbrproxyimpndv", {"A": A, "r": r, "u": u, "v": v},
        (h_aset,)
    )[0]

    VEQ = eq(v, C)
    p_req_id_v = ap(b, "a1i", {"ph": bi(REQ, REQ), "ps": VEQ},
                      (ap(b, "biid", {"ph": REQ})[0],))[0]
    p_u_mem_id = ap(b, "a1i", {"ph": bi(mem(u, H), mem(u, H)), "ps": VEQ},
                       (ap(b, "biid", {"ph": mem(u, H)})[0],))[0]
    p_v_mem = ap(b, "eleq1d", {"ph": VEQ, "A": v, "B": C, "C": H},
                 (ap(b, "id", {"ph": VEQ})[0],))[0]
    p_ends_v = ap(
        b, "anbi12d",
        {"ph": VEQ, "ps": mem(u, H), "ch": mem(u, H),
         "th": mem(v, H), "ta": mem(C, H)},
        (p_u_mem_id, p_v_mem)
    )[0]
    p_ant_v = ap(
        b, "anbi12d",
        {"ph": VEQ, "ps": REQ, "ch": REQ, "th": GUV, "ta": GUC},
        (p_req_id_v, p_ends_v)
    )[0]
    p_v_class = ap(b, "eceq1", {"A": v, "B": C, "C": ISO})[0]
    p_left_v = ap(
        b, "breq2d", {"ph": VEQ, "A": qs(v, ISO), "B": qs(C, ISO),
                       "C": qs(u, ISO), "R": L}, (p_v_class,)
    )[0]
    p_right_v = ap(
        b, "breq2d", {"ph": VEQ, "A": v, "B": C, "C": u, "R": CMP},
        (ap(b, "id", {"ph": VEQ})[0],)
    )[0]
    p_body_v = ap(
        b, "bibi12d", {"ph": VEQ, "ps": LUV, "ch": LUC,
                        "th": RUV, "ta": RUC}, (p_left_v, p_right_v)
    )[0]
    p_t_v = ap(
        b, "imbi12d", {"ph": VEQ, "ps": conj(REQ, GUV),
                        "ch": conj(REQ, GUC), "th": bi(LUV, RUV),
                        "ta": bi(LUC, RUC)}, (p_ant_v, p_body_v)
    )[0]
    p_c_guard = ap(
        b, "vtoclg", {"x": v, "A": C, "V": V, "ph": TUV, "ps": TUC},
        (p_t_v, p_base)
    )[0]
    p_c_to_t = ap(
        b, "syl", {"ph": mem(C, H), "ps": mem(C, V), "ch": TUC},
        (ap(b, "elex", {"A": C, "B": H})[0], p_c_guard)
    )[0]

    UEQ = eq(u, B)
    p_req_id_u = ap(b, "a1i", {"ph": bi(REQ, REQ), "ps": UEQ},
                      (ap(b, "biid", {"ph": REQ})[0],))[0]
    p_c_mem_id = ap(b, "a1i", {"ph": bi(mem(C, H), mem(C, H)), "ps": UEQ},
                       (ap(b, "biid", {"ph": mem(C, H)})[0],))[0]
    p_u_mem = ap(b, "eleq1d", {"ph": UEQ, "A": u, "B": B, "C": H},
                 (ap(b, "id", {"ph": UEQ})[0],))[0]
    p_ends_u = ap(
        b, "anbi12d",
        {"ph": UEQ, "ps": mem(u, H), "ch": mem(B, H),
         "th": mem(C, H), "ta": mem(C, H)},
        (p_u_mem, p_c_mem_id)
    )[0]
    p_ant_u = ap(
        b, "anbi12d",
        {"ph": UEQ, "ps": REQ, "ch": REQ, "th": GUC, "ta": GBC},
        (p_req_id_u, p_ends_u)
    )[0]
    p_u_class = ap(b, "eceq1", {"A": u, "B": B, "C": ISO})[0]
    p_left_u = ap(
        b, "breq1d", {"ph": UEQ, "A": qs(u, ISO), "B": qs(B, ISO),
                       "C": qs(C, ISO), "R": L}, (p_u_class,)
    )[0]
    p_right_u = ap(
        b, "breq1d", {"ph": UEQ, "A": u, "B": B, "C": C, "R": CMP},
        (ap(b, "id", {"ph": UEQ})[0],)
    )[0]
    p_body_u = ap(
        b, "bibi12d", {"ph": UEQ, "ps": LUC, "ch": LBC,
                        "th": RUC, "ta": RBC}, (p_left_u, p_right_u)
    )[0]
    p_t_u = ap(
        b, "imbi12d", {"ph": UEQ, "ps": conj(REQ, GUC),
                        "ch": conj(REQ, GBC), "th": bi(LUC, RUC),
                        "ta": bi(LBC, RBC)}, (p_ant_u, p_body_u)
    )[0]
    p_c_imp_cong = ap(
        b, "imbi12d", {"ph": UEQ, "ps": mem(C, H), "ch": mem(C, H),
                        "th": TUC, "ta": TBC}, (p_c_mem_id, p_t_u)
    )[0]
    p_b_guard = ap(
        b, "vtoclg", {"x": u, "A": B, "V": V,
                       "ph": imp(mem(C, H), TUC),
                       "ps": imp(mem(C, H), TBC)},
        (p_c_imp_cong, p_c_to_t)
    )[0]

    p_g_b = ap(b, "simpl", {"ph": mem(B, H), "ps": mem(C, H)})[0]
    p_g_c = ap(b, "simpr", {"ph": mem(B, H), "ps": mem(C, H)})[0]
    p_g_bset = ap(
        b, "syl", {"ph": GBC, "ps": mem(B, H), "ch": mem(B, V)},
        (p_g_b, ap(b, "elex", {"A": B, "B": H})[0])
    )[0]
    p_g_ct = ap(
        b, "syl", {"ph": GBC, "ps": mem(B, V),
                    "ch": imp(mem(C, H), TBC)}, (p_g_bset, p_b_guard)
    )[0]
    p_g_tbc = ap(
        b, "mpd", {"ph": GBC, "ps": mem(C, H), "ch": TBC},
        (p_g_c, p_g_ct)
    )[0]
    ctx = conj(REQ, GBC)
    p_ctx_g = ap(b, "simpr", {"ph": REQ, "ps": GBC})[0]
    p_ctx_tbc = ap(
        b, "syl", {"ph": ctx, "ps": GBC, "ch": TBC},
        (p_ctx_g, p_g_tbc)
    )[0]
    p_final = ap(
        b, "mpd", {"ph": ctx, "ps": ctx, "ch": bi(LBC, RBC)},
        (ap(b, "id", {"ph": ctx})[0], p_ctx_tbc)
    )[0]

    assert db.stmts[LABEL].expr == ("|-",) + TBC
    proof = compressed(db, LABEL, p_final)
    out_text = PRE.read_text(encoding="utf-8")
    start = out_text.index(LABEL + " $p")
    hole = out_text.index("$= ? $.", start)
    out_text = out_text[:hole] + "$= " + proof + " $." + out_text[hole + len("$= ? $."):]
    OUT.write_text(out_text, encoding="utf-8", newline="\n")
    mpb.load(OUT, verify=True, allow_incomplete=False)
    print(OUT)


if __name__ == "__main__":
    main()
