"""Freeze a BE2D-compatible parent-free value + ambient-order tail."""

from hashlib import sha256
from pathlib import Path
import json
import importlib.util
import gc
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BASE = ROOT / "work/mm0_conversion_2026-08-20/toolchain/hnwcut_strict_quotient_stage3/strict_quotient_imp_frozen_checkpoint.mm"
BASE_SHA = "BE2D112F89516EED24DCB972EA1B2792A95590547D2E9823903C73312C3DFBB1"
NOAR = ROOT / "work/mm0_conversion_2026-08-20/source_repair/hnwcut_alias/factorval_no_ar_reemit_test.mm"
CODE = ROOT / "work/mm0_conversion_2026-08-20/source_repair/hnwcut_alias/factorval_code_stage_checkpoint.mm"
VALUE = HERE / "factor_value_imp_live.mm"
AMBIENT = ROOT / "work/mm0_conversion_2026-08-20/toolchain/hnwcut_ambient_order_stage4/ambient_order_imp_parent_free_suffix.mm"
AMBIENT_DONOR = ROOT / "work/mm0_conversion_2026-08-20/toolchain/hnwcut_ambient_order_stage4/ambient_order_imp_with_factor_hole_live.mm"
MPB = ROOT / "formalization_continue/reconstruct/mmproof_builder_current.py"
SUFFIX = HERE / "value_ambient_be2d_parent_free_suffix.mm"
CHECKPOINT = HERE / "value_ambient_be2d_frozen_checkpoint.mm"
AUDIT = HERE / "value_ambient_be2d_audit.json"
MARKER = "$( Linear replay source: C:/Users/glaze/Documents/Codex/2026-08-16/study-the-contents-of-this-and/work/formalization_continue/hnord_wellorder/hnwcut_ambient_strict_segment_isom_alias_checkpoint.mm $)"

spec=importlib.util.spec_from_file_location("hnwcut_value_ambient_recompress",MPB)
assert spec and spec.loader
mpb=importlib.util.module_from_spec(spec);sys.modules[spec.name]=mpb;spec.loader.exec_module(mpb)

def extract_block(path: Path, label: str) -> str:
    text=path.read_text(encoding="utf-8"); pos=text.index(label+" $p")
    toks=list(re.finditer(r"\$\{|\$\}",text)); stack=[]
    for t in toks:
        if t.start()>=pos: break
        if t.group()=="${": stack.append(t.start())
        elif stack: stack.pop()
    if not stack: raise RuntimeError(f"no block for {label}")
    start=stack[-1]; depth=0
    for t in toks:
        if t.start()<start: continue
        depth += 1 if t.group()=="${" else -1
        if depth==0: return text[start:t.end()]
    raise RuntimeError(f"unterminated block {label}")

def remove_local_floats(block: str) -> str:
    """Use the active BE2D floats instead of duplicating them locally.

    A copied local float and an already-active global float for the same
    metavariable both become mandatory in a flattened insertion.  That changes
    the arity of every new helper and invalidates later donor applications.
    Removing only the local `$f` statements leaves the theorem expressions and
    proof DAGs unchanged while restoring the donor mandatory-hypothesis arity.
    """
    float_line = re.compile(
        r"(?m)^\s*([A-Za-z0-9_.-]+)\s+\$f\s+(?:wff|class|setvar)\s+"
        r"[A-Za-z0-9_.-]+\s+\$\.\s*\r?\n"
    )
    # `x` is a genuinely proof-local abstraction variable in the code
    # congruence theorem, so its float must remain available.  Every other
    # local float occurs in its theorem assertion and is replaced by the
    # corresponding active BE2D float.
    return float_line.sub(
        lambda m: m.group(0) if m.group(1) == "hnwcutcodeeq-vx" else "",
        block,
    )

def proof_span(text: str, label: str):
    p=text.index(label+" $p"); a=text.index("$=",p)+2; b=text.index("$.",a)
    return a,b,text[a:b].strip()

def decode(code: str):
    out=[]; acc=0
    for ch in code:
        if "U"<=ch<="Y": acc=5*acc+(ord(ch)-ord("U")+1)
        elif "A"<=ch<="T":
            out.append(20*acc+(ord(ch)-ord("A")+1));acc=0
        elif ch=="Z": out.append("Z")
        elif not ch.isspace(): raise ValueError(f"bad compressed char {ch!r}")
    if acc: raise ValueError("unterminated compressed number")
    return out

def enc(n: int):
    q,last=divmod(n-1,20); pre=[]
    while q:q,d=divmod(q-1,5);pre.append(chr(ord("U")+d))
    return "".join(reversed(pre))+chr(ord("A")+last)

def remap_proof(donor_text, donor_db, new_db, label):
    """Decode a donor proof DAG and re-emit it in target assertion order.

    A flat numeric-table rewrite is insufficient when a newly declared helper
    has a different mandatory-float order in the flattened BE2D context: every
    later application of that helper must have its child proofs permuted.  This
    routine reconstructs assertion nodes with the donor mandatory order, then
    recursively permutes their children to the target mandatory order by
    matching hypothesis kind and formal expression.  The result is compressed
    without saved-node references; these bounded helper proofs are small.
    """
    _,_,raw=proof_span(donor_text,label); toks=raw.split()
    if not toks or toks[0]!="(": raise ValueError(f"uncompressed donor {label}")
    close=toks.index(")"); extras=toks[1:close]; code="".join(toks[close+1:])
    oldtable=list(donor_db.stmts[label].mand_hyps)+extras

    # A node is [label, children].  Saved references deliberately share nodes;
    # emission below may duplicate them, which is semantically harmless.
    stack=[]; saved=[]
    for item in decode(code):
        if item=="Z":
            if not stack: raise ValueError(f"{label}: save on empty stack")
            saved.append(stack[-1]); continue
        if item<=len(oldtable):
            lab=oldtable[item-1]
            st=donor_db.stmts[lab]
            if st.kind in ("$f","$e"):
                stack.append([lab,[]]); continue
            arity=len(st.mand_hyps)
            if len(stack)<arity: raise ValueError(f"{label}: underflow at {lab}")
            children=stack[-arity:] if arity else []
            if arity: del stack[-arity:]
            stack.append([lab,children]); continue
        sidx=item-len(oldtable)-1
        if sidx<0 or sidx>=len(saved):
            raise ValueError(f"{label}: bad saved reference {item}")
        stack.append(saved[sidx])
    if len(stack)!=1: raise ValueError(f"{label}: final stack size {len(stack)}")

    def hyp_key(db,h):
        st=db.stmts[h]
        return st.kind,st.expr

    def target_leaf(old):
        if old in new_db.stmts:return old
        key=hyp_key(donor_db,old)
        hits=[h for h,s in new_db.stmts.items() if (s.kind,s.expr)==key]
        if not hits: raise KeyError(f"{label}: no target leaf for {old} {key}")
        # Active global floats occur early; proof-local floats retain their
        # exact label and are handled by the branch above.
        return hits[-1]

    def retarget(node):
        lab,children=node
        if not children:
            return [target_leaf(lab),[]]
        if lab not in new_db.stmts:
            raise KeyError(f"{label}: target lacks assertion {lab}")
        oldhyps=list(donor_db.stmts[lab].mand_hyps)
        newhyps=list(new_db.stmts[lab].mand_hyps)
        if len(children)!=len(oldhyps):
            raise ValueError(f"{label}: child/mandatory mismatch at {lab}")
        used=set(); ordered=[]
        for nh in newhyps:
            candidates=[i for i,oh in enumerate(oldhyps)
                        if i not in used and hyp_key(donor_db,oh)==hyp_key(new_db,nh)]
            if not candidates:
                raise KeyError(f"{label}: cannot align {lab}/{nh}")
            i=candidates[0];used.add(i);ordered.append(retarget(children[i]))
        return [lab,ordered]

    proof=[]
    def emit(node):
        lab,children=node
        for child in children: emit(child)
        proof.append(lab)
    emit(retarget(stack[0]))

    mandatory=list(new_db.stmts[label].mand_hyps); extra=[]
    for tok in proof:
        if tok not in mandatory and tok not in extra: extra.append(tok)
    table=mandatory+extra
    return "( "+" ".join(extra)+" ) "+"".join(enc(table.index(tok)+1) for tok in proof)

def main():
    actual=sha256(BASE.read_bytes()).hexdigest().upper()
    if actual!=BASE_SHA: raise RuntimeError(f"unexpected BE2D parent {actual}")
    labels=[
        (NOAR,"hnwcutrelambfnnoarndv"),
        (NOAR,"hnwcutambfactorvalnoarndv"),
        (CODE,"hnwcutambfactorvalcodendv"),
        (VALUE,"hnwcuttxpeq1dndv"),
        (VALUE,"hnwcutimageeqdndv"),
        (VALUE,"hnwcutreleq12dndv"),
        (VALUE,"hnwcutcodeeq12clndv"),
        (VALUE,"hnwcutambfactorvalimpclndv"),
        (VALUE,"hnwcutambfactorvalimpndv"),
        (AMBIENT,"hnwcutambordbrproxyimpndv"),
    ]
    blocks=[remove_local_floats(extract_block(p,l)) for p,l in labels]
    suffix="$( BE2D-compatible value and conditional ambient-order tail. $)\n\n"+"\n\n".join(blocks)+"\n"
    SUFFIX.write_text(suffix,encoding="utf-8",newline="\n")
    base=BASE.read_text(encoding="utf-8")
    if base.count(MARKER)!=1: raise RuntimeError("alias marker not unique")
    for _,lab in labels:
        if lab in base: raise RuntimeError(f"duplicate label in BE2D parent: {lab}")
    checkpoint=base.replace(MARKER,suffix+"\n"+MARKER,1)
    CHECKPOINT.write_text(checkpoint,encoding="utf-8",newline="\n")

    # Every copied theorem is recompressed against the actual BE2D mandatory
    # hypothesis table.  This removes stale offsets caused by outer global
    # floating hypotheses while preserving the donor proof token stream.
    new_db=mpb.load(CHECKPOINT,verify=False,allow_incomplete=False)
    donors={NOAR:["hnwcutrelambfnnoarndv","hnwcutambfactorvalnoarndv"],
            CODE:["hnwcutambfactorvalcodendv"],
            VALUE:["hnwcuttxpeq1dndv","hnwcutimageeqdndv","hnwcutreleq12dndv",
                   "hnwcutcodeeq12clndv","hnwcutambfactorvalimpclndv",
                   "hnwcutambfactorvalimpndv"],
            AMBIENT_DONOR:["hnwcutambordbrproxyimpndv"]}
    checkpoint=CHECKPOINT.read_text(encoding="utf-8"); suffix=SUFFIX.read_text(encoding="utf-8")
    for donor_path, group in donors.items():
        donor_db=mpb.load(donor_path,verify=False,allow_incomplete=True)
        donor_text=donor_path.read_text(encoding="utf-8")
        for label in group:
            proof=remap_proof(donor_text,donor_db,new_db,label)
            a,b,_=proof_span(checkpoint,label);checkpoint=checkpoint[:a]+" "+proof+" "+checkpoint[b:]
            a,b,_=proof_span(suffix,label);suffix=suffix[:a]+" "+proof+" "+suffix[b:]
        del donor_db;gc.collect()
    CHECKPOINT.write_text(checkpoint,encoding="utf-8",newline="\n")
    SUFFIX.write_text(suffix,encoding="utf-8",newline="\n")
    AUDIT.write_text(json.dumps({
        "schema":"hnwcut-value-ambient-be2d-audit-v1",
        "parent":str(BASE.relative_to(ROOT)),"parent_sha256":BASE_SHA,
        "checkpoint":str(CHECKPOINT.relative_to(ROOT)),
        "checkpoint_sha256":sha256(CHECKPOINT.read_bytes()).hexdigest().upper(),
        "parent_free_suffix":str(SUFFIX.relative_to(ROOT)),
        "parent_free_suffix_sha256":sha256(SUFFIX.read_bytes()).hexdigest().upper(),
        "labels":[l for _,l in labels],
        "inserted_before_inherited_alias0":True,
    },indent=2)+"\n",encoding="utf-8",newline="\n")
    print(CHECKPOINT);print(SUFFIX)

if __name__=="__main__": main()
