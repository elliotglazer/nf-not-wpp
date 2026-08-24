"""Build a strict quotient comparator theorem with all proxy facts internalized.

This is a small, manual DAG proof.  It intentionally does not invoke the
recursive deduction transformer.
"""

from hashlib import sha256
from pathlib import Path
import importlib.util
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BASE = (
    ROOT
    / "work/mm0_conversion_2026-08-20/source_repair/hnwcut_resisomr_assist"
    / "quotient_proxy_imp_class_stage2_checkpoint.mm"
)
EXPECTED_BASE_SHA256 = (
    "24A5D458B22747CFBD172326293548BD4EF56BC08DD11908AC91E6A8AB57335A"
)
PRE = HERE / "strict_quotient_imp_pre.mm"
OUT = HERE / "strict_quotient_imp_live.mm"
FROZEN = HERE / "strict_quotient_imp_frozen_checkpoint.mm"
SUFFIX = HERE / "strict_quotient_imp_parent_free_suffix.mm"
MPB = ROOT / "formalization_continue/reconstruct/mmproof_builder_current.py"

MARKER = "$( Linear replay source: C:/Users/glaze/Documents/Codex/2026-08-16/study-the-contents-of-this-and/work/formalization_continue/hnord_wellorder/hnwcut_ambient_strict_segment_isom_alias_checkpoint.mm $)"
LABEL = "hncodecmpquotstrictbrproxyimpclndv"

BLOCK = r"""$( Deduction-form strict quotient comparator law with class endpoints. $)
${
  $d A r $.
  hncodecmpquotstrictbrproxyimpclndv.1 $e |- A e. _V $.
  hncodecmpquotstrictbrproxyimpclndv $p |- (
    ( r = HNCodeCmpSet A /\
      ( B e. HWCN A /\ C e. HWCN A ) ) ->
    ( [ B ] HWNIso A
        ( LNQOrd ( r , HWCN A ) \ _I )
      [ C ] HWNIso A
      <-> B ( HNCodeCmpSet A \ `' HNCodeCmpSet A ) C ) ) $= ? $.
$}"""


def prepare_pre() -> None:
    data = BASE.read_bytes()
    digest = sha256(data).hexdigest().upper()
    if digest != EXPECTED_BASE_SHA256:
        raise RuntimeError(f"unexpected stage-2 parent SHA256: {digest}")
    text = data.decode("utf-8")
    if LABEL in text:
        raise RuntimeError(f"{LABEL} already occurs in the parent")
    if text.count(MARKER) != 1:
        raise RuntimeError("expected a unique HNWCut alias replay marker")
    PRE.write_text(text.replace(MARKER, BLOCK + "\n\n" + MARKER, 1), encoding="utf-8", newline="\n")


spec = importlib.util.spec_from_file_location("hnwcut_strict_quotient_imp_builder", MPB)
assert spec is not None and spec.loader is not None
mpb = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mpb
spec.loader.exec_module(mpb)


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
def br(a, rel, c): return flat(a, rel, c)
def par(*parts): return flat("(", *parts, ")")
def qs(a, rel): return flat("[", a, "]", rel)


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
    prepare_pre()
    db = mpb.load(PRE, verify=False, allow_incomplete=True)
    b = mpb.Builder(db)

    def ap(label, subst=None, essentials=()):
        return b.apply(label, subst or {}, list(essentials))

    A = ("A",); r = ("r",); B = ("B",); C = ("C",)
    V = ("_V",)
    CMP = flat("HNCodeCmpSet", A)
    H = flat("HWCN", A)
    ISO = flat("HWNIso", A)
    L = flat("LNQOrd", "(", r, ",", H, ")")
    KR = flat("LNKer", r)
    KC = flat("LNKer", CMP)
    ASET = mem(A, V)
    REQ = eq(r, CMP)
    BM = mem(B, H)
    CM = mem(C, H)
    G = conj(BM, CM)
    CTX = conj(REQ, G)

    h_aset = ap(LABEL + ".1")[0]
    c_req = ap("simpl", {"ph": REQ, "ps": G})[0]
    c_g = ap("simpr", {"ph": REQ, "ps": G})[0]
    c_aset = ap("a1i", {"ph": ASET, "ps": CTX}, (h_aset,))[0]
    g_bm = ap("simpl", {"ph": BM, "ps": CM})[0]
    g_cm = ap("simpr", {"ph": BM, "ps": CM})[0]
    c_bm = ap("syl", {"ph": CTX, "ps": G, "ch": BM}, (c_g, g_bm))[0]
    c_cm = ap("syl", {"ph": CTX, "ps": G, "ch": CM}, (c_g, g_cm))[0]

    CSET = mem(CMP, V)
    HSET = mem(H, V)
    RSET = mem(r, V)
    c_cset = ap(
        "syl",
        {"ph": CTX, "ps": ASET, "ch": CSET},
        (c_aset, ap("hncodecmpsetexg", {"A": A})[0]),
    )[0]
    c_hset = ap(
        "syl",
        {"ph": CTX, "ps": ASET, "ch": HSET},
        (c_aset, ap("hwcnexg", {"A": A})[0]),
    )[0]
    c_rset_bi = ap(
        "eleq1d", {"ph": CTX, "A": r, "B": CMP, "C": V}, (c_req,)
    )[0]
    c_rset = ap(
        "mpbird", {"ph": CTX, "ps": RSET, "ch": CSET}, (c_cset, c_rset_bi)
    )[0]

    HXH = par(H, "X.", H)
    CREF = br(CMP, "Ref", H); RREF = br(r, "Ref", H)
    CTRANS = br(CMP, "Trans", H); RTRANS = br(r, "Trans", H)
    CCONN = br(CMP, "Connex", H); RCONN = br(r, "Connex", H)
    CSS = flat(CMP, "C_", HXH); RSS = flat(r, "C_", HXH)

    def cmp_fact(label, target):
        return ap(
            "syl",
            {"ph": CTX, "ps": ASET, "ch": target},
            (c_aset, ap(label, {"A": A})[0]),
        )[0]

    c_cref = cmp_fact("hncodecmpsetrefndv", CREF)
    c_ctrans = cmp_fact("hncodecmpsettransndv", CTRANS)
    c_cconn = cmp_fact("hncodecmpsetconnexndv", CCONN)
    c_css = ap(
        "a1i", {"ph": CSS, "ps": CTX}, (ap("hncodecmpsetssxpndv", {"A": A})[0],)
    )[0]

    def transport_property(cprop, rprop, proof, rel):
        equiv = ap(
            "breq1d", {"ph": CTX, "A": r, "B": CMP, "C": H, "R": rel}, (c_req,)
        )[0]
        return ap(
            "mpbird", {"ph": CTX, "ps": rprop, "ch": cprop}, (proof, equiv)
        )[0]

    c_rref = transport_property(CREF, RREF, c_cref, ("Ref",))
    c_rtrans = transport_property(CTRANS, RTRANS, c_ctrans, ("Trans",))
    c_rconn = transport_property(CCONN, RCONN, c_cconn, ("Connex",))
    c_ss_bi = ap(
        "sseq1d", {"ph": CTX, "A": r, "B": CMP, "C": HXH}, (c_req,)
    )[0]
    c_rss = ap(
        "mpbird", {"ph": CTX, "ps": RSS, "ch": CSS}, (c_css, c_ss_bi)
    )[0]

    RTC = conj(conj(RREF, RTRANS), RCONN)
    ORDER = conj(RTC, RSS)
    SETS = conj(RSET, HSET)
    SETORDER = conj(SETS, ORDER)
    ENDS = conj(BM, CM)
    ANT = conj(SETORDER, ENDS)
    c_rt = ap("jca", {"ph": CTX, "ps": RREF, "ch": RTRANS}, (c_rref, c_rtrans))[0]
    c_rtc = ap(
        "jca", {"ph": CTX, "ps": conj(RREF, RTRANS), "ch": RCONN}, (c_rt, c_rconn)
    )[0]
    c_order = ap("jca", {"ph": CTX, "ps": RTC, "ch": RSS}, (c_rtc, c_rss))[0]
    c_sets = ap("jca", {"ph": CTX, "ps": RSET, "ch": HSET}, (c_rset, c_hset))[0]
    c_setorder = ap(
        "jca", {"ph": CTX, "ps": SETS, "ch": ORDER}, (c_sets, c_order)
    )[0]
    c_ends = ap("jca", {"ph": CTX, "ps": BM, "ch": CM}, (c_bm, c_cm))[0]
    c_ant = ap(
        "jca", {"ph": CTX, "ps": SETORDER, "ch": ENDS}, (c_setorder, c_ends)
    )[0]

    STRICT_L = par(L, "\\", ("_I",))
    STRICT_R = par(r, "\\", flat("`'", r))
    QB_RAW = qs(B, KR)
    QC_RAW = qs(C, KR)
    RAW = bi(br(QB_RAW, STRICT_L, QC_RAW), br(B, STRICT_R, C))
    c_raw = ap(
        "syl",
        {"ph": CTX, "ps": ANT, "ch": RAW},
        (c_ant, ap("brlnqordstrict", {"R": r, "C": H, "X": B, "Y": C})[0]),
    )[0]

    c_lnkereq = ap(
        "syl", {"ph": CTX, "ps": REQ, "ch": eq(KR, KC)},
        (c_req, ap("lnkereq", {"R": r, "S": CMP})[0]),
    )[0]
    c_kerc = ap(
        "syl", {"ph": CTX, "ps": ASET, "ch": eq(KC, ISO)},
        (c_aset, ap("hncodecmplnkerndv", {"A": A})[0]),
    )[0]
    c_ker = ap(
        "eqtrd", {"ph": CTX, "A": KR, "B": KC, "C": ISO}, (c_lnkereq, c_kerc)
    )[0]
    c_qb = ap(
        "syl", {"ph": CTX, "ps": eq(KR, ISO), "ch": eq(QB_RAW, qs(B, ISO))},
        (c_ker, ap("eceq2", {"A": KR, "B": ISO, "C": B})[0]),
    )[0]
    c_qc = ap(
        "syl", {"ph": CTX, "ps": eq(KR, ISO), "ch": eq(QC_RAW, qs(C, ISO))},
        (c_ker, ap("eceq2", {"A": KR, "B": ISO, "C": C})[0]),
    )[0]
    LEFT_RAW = br(QB_RAW, STRICT_L, QC_RAW)
    LEFT = br(qs(B, ISO), STRICT_L, qs(C, ISO))
    c_left = ap(
        "breq12d",
        {"ph": CTX, "A": QB_RAW, "B": qs(B, ISO), "C": QC_RAW,
         "D": qs(C, ISO), "R": STRICT_L},
        (c_qb, c_qc),
    )[0]
    c_left_rev = ap(
        "bicomd", {"ph": CTX, "ps": LEFT_RAW, "ch": LEFT}, (c_left,)
    )[0]

    CSTRICT = par(CMP, "\\", flat("`'", CMP))
    RIGHT_RAW = br(B, STRICT_R, C)
    RIGHT = br(B, CSTRICT, C)
    c_cnv = ap("cnveqd", {"ph": CTX, "A": r, "B": CMP}, (c_req,))[0]
    c_strict_eq = ap(
        "difeq12d",
        {"ph": CTX, "A": r, "B": CMP, "C": flat("`'", r), "D": flat("`'", CMP)},
        (c_req, c_cnv),
    )[0]
    c_right = ap(
        "breqd", {"ph": CTX, "A": STRICT_R, "B": CSTRICT, "C": B, "D": C},
        (c_strict_eq,),
    )[0]
    c_right_rev = ap(
        "bicomd", {"ph": CTX, "ps": RIGHT_RAW, "ch": RIGHT}, (c_right,)
    )[0]
    c_final = ap(
        "3bitr4d",
        {"ph": CTX, "ps": LEFT_RAW, "ch": RIGHT_RAW, "th": LEFT, "ta": RIGHT},
        (c_raw, c_left_rev, c_right_rev),
    )[0]

    target = ("|-",) + imp(CTX, bi(LEFT, RIGHT))
    if db.stmts[LABEL].expr != target:
        raise RuntimeError("target expression mismatch")

    text = PRE.read_text(encoding="utf-8").replace(
        "$= ? $.", "$= " + compressed(db, LABEL, c_final) + " $.", 1
    )
    OUT.write_text(text, encoding="utf-8", newline="\n")
    mpb.load(OUT, verify=True, allow_incomplete=False)
    FROZEN.write_text(text, encoding="utf-8", newline="\n")
    block_start = text.index("$( Deduction-form strict quotient comparator law")
    block_end = text.index(MARKER, block_start)
    SUFFIX.write_text(text[block_start:block_end].rstrip() + "\n", encoding="utf-8", newline="\n")
    print(OUT)


if __name__ == "__main__":
    main()
