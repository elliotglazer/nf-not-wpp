#!/usr/bin/env python3
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Set
import sys

@dataclass
class Hyp:
    label: str
    kind: str
    expr: Tuple[str,...]
    var: Optional[str]=None

@dataclass
class Assertion:
    label: str
    kind: str
    expr: Tuple[str,...]
    hyps: Tuple[str,...]
    dv: Tuple[Tuple[str,str],...]
    proof: Optional[Tuple[str,...]]=None

class Database:
    def __init__(self):
        self.constants:Set[str]=set(); self.variables:Set[str]=set()
        self.labels:Dict[str,object]={}; self.hyps:Dict[str,Hyp]={}
        self.var_f:Dict[str,str]={}; self.frames=[]; self.included=set()
        self.proof_count=0; self.statement_count=0
    @property
    def vars(self): return self.variables
    @property
    def stmts(self): return self.labels
    def subst_expr(self, expr, subst):
        out=[]
        for t in expr:
            if t in self.variables and t in subst: out.extend(subst[t])
            else: out.append(t)
        return tuple(out)
    def tokenize(self,text):
        toks=[]; i=0; n=len(text)
        while i<n:
            if text.startswith('$(',i):
                j=text.find('$)',i+2)
                if j<0: raise ValueError('unterminated comment')
                i=j+2; continue
            if text[i].isspace(): i+=1; continue
            j=i
            while j<n and not text[j].isspace() and not text.startswith('$(',j): j+=1
            toks.append(text[i:j]); i=j
        return toks
    def active_hyps(self):
        out=[]
        for fr in self.frames: out.extend(fr['hyps'])
        return out
    def active_dv(self):
        out=set()
        for fr in self.frames: out |= fr['dv']
        return out
    def add_assertion(self,label,kind,expr,proof=None):
        active=self.active_hyps()
        essentials=[h for h in active if self.hyps[h].kind=='$e']
        mand_vars=set(t for t in expr if t in self.variables)
        for h in essentials: mand_vars |= set(t for t in self.hyps[h].expr if t in self.variables)
        floats=[h for h in active if self.hyps[h].kind=='$f' and self.hyps[h].var in mand_vars]
        # mandatory hypotheses in declaration order, but only required floats and all essentials
        mand=tuple(h for h in active if h in floats or h in essentials)
        dv=[]
        for x,y in self.active_dv():
            if x in mand_vars and y in mand_vars: dv.append(tuple(sorted((x,y))))
        st=Assertion(label,kind,tuple(expr),mand,tuple(sorted(set(dv))),tuple(proof) if proof else None)
        self.labels[label]=st; self.statement_count+=1
        return st
    def parse_file(self,path,verify=True,allow_incomplete=False):
        path=Path(path).resolve()
        if path in self.included:return
        self.included.add(path)
        toks=self.tokenize(path.read_text(errors='replace')); i=0
        if not self.frames:self.frames=[{'hyps':[],'dv':set()}]
        while i<len(toks):
            tok=toks[i]
            if tok=='${': self.frames.append({'hyps':[],'dv':set()}); i+=1; continue
            if tok=='$}': self.frames.pop(); i+=1; continue
            if tok=='$[':
                inc=toks[i+1]; assert toks[i+2]=='$]'; self.parse_file(path.parent/inc,verify,allow_incomplete); i+=3; continue
            if tok in ('$c','$v','$d'):
                j=i+1
                vals=[]
                while toks[j]!='$.': vals.append(toks[j]); j+=1
                if tok=='$c': self.constants.update(vals)
                elif tok=='$v': self.variables.update(vals)
                else:
                    for a in range(len(vals)):
                        for b in range(a+1,len(vals)):
                            self.frames[-1]['dv'].add(tuple(sorted((vals[a],vals[b]))))
                i=j+1; continue
            label=tok; typ=toks[i+1]
            if typ in ('$f','$e'):
                j=i+2; expr=[]
                while toks[j]!='$.':expr.append(toks[j]);j+=1
                var=expr[1] if typ=='$f' and len(expr)==2 else None
                h=Hyp(label,typ,tuple(expr),var); self.hyps[label]=h; self.labels[label]=h
                self.frames[-1]['hyps'].append(label); self.statement_count+=1
                if var:self.var_f[var]=label
                i=j+1;continue
            if typ in ('$a','$p'):
                j=i+2;expr=[]
                while toks[j] not in ('$=','$.'):expr.append(toks[j]);j+=1
                if typ=='$a':
                    assert toks[j]=='$.'; self.add_assertion(label,typ,expr);i=j+1;continue
                assert toks[j]=='$='; j+=1; proof=[]
                while toks[j]!='$.':proof.append(toks[j]);j+=1
                st=self.add_assertion(label,typ,expr,proof)
                if verify and not (proof==['?'] and allow_incomplete): self.verify_proof(st,proof)
                elif proof==['?'] and not allow_incomplete: raise ValueError(f'incomplete proof {label}')
                if proof!=['?']: self.proof_count+=1
                i=j+1;continue
            raise ValueError(f'unknown token at {i}: {tok} {typ}')
    def _decode_compressed(self, proof, st):
        # proof = ( labels ) encoded tokens (possibly split)
        assert proof[0]=='('
        k=proof.index(')'); labels=list(st.hyps)+proof[1:k]
        code=''.join(proof[k+1:]); nums=[]; acc=0
        for ch in code:
            if ch.isspace():continue
            if ch=='Z': nums.append(-1); continue
            o=ord(ch)
            if ord('A')<=o<=ord('T'):
                acc=20*acc+(o-ord('A')+1); nums.append(acc-1); acc=0
            elif ord('U')<=o<=ord('Y'):
                acc=5*acc+(o-ord('U')+1)
            else: raise ValueError(f'bad compressed char {ch!r} in {st.label}')
        return labels,nums
    def verify_proof(self,st,proof):
        stack=[]; saved=[]
        if proof and proof[0]=='(':
            labels,seq=self._decode_compressed(proof,st)
            items=[]
            for n in seq:
                if n==-1: items.append(('save',None))
                elif n<len(labels): items.append(('label',labels[n]))
                else: items.append(('saved',n-len(labels)))
        else: items=[('label',x) for x in proof]
        for kind,val in items:
            if kind=='save':
                if not stack: raise ValueError(f'{st.label}: save empty')
                saved.append(stack[-1]); continue
            if kind=='saved':
                if val<0 or val>=len(saved):raise ValueError(f'{st.label}: bad saved {val}')
                stack.append(saved[val]);continue
            lab=val
            if lab not in self.labels: raise ValueError(f'{st.label}: unknown label {lab}')
            obj=self.labels[lab]
            if isinstance(obj,Hyp): stack.append(obj.expr);continue
            nh=len(obj.hyps)
            if len(stack)<nh: raise ValueError(f'{st.label}: stack underflow applying {lab}')
            args=stack[-nh:] if nh else []; del stack[len(stack)-nh:]
            subst={}; ai=0
            for hl in obj.hyps:
                h=self.hyps[hl]; got=args[ai]; ai+=1
                if h.kind=='$f':
                    if not got or got[0]!=h.expr[0]: raise ValueError(f'{st.label}: type mismatch {lab}/{hl}')
                    subst[h.var]=got[1:]
                else:
                    want=self.subst_expr(h.expr,subst)
                    if got!=want: raise ValueError(f'{st.label}: hyp mismatch {lab}/{hl}\n got {got}\nwant {want}')
            # DV: variables occurring in substitutions must be disjoint for each mandated pair
            for x,y in obj.dv:
                sx=set(t for t in subst.get(x,()) if t in self.variables)
                sy=set(t for t in subst.get(y,()) if t in self.variables)
                if sx & sy: raise ValueError(f'{st.label}: DV violation applying {lab}: {x},{y}, common {sx&sy}')
                for u in sx:
                    for v in sy:
                        if tuple(sorted((u,v))) not in self.active_dv():
                            raise ValueError(f'{st.label}: missing active DV {u},{v} applying {lab}')
            stack.append(self.subst_expr(obj.expr,subst))
        if len(stack)!=1 or stack[0]!=st.expr:
            raise ValueError(f'{st.label}: final stack mismatch\nstack={stack[-3:]}\nwant={st.expr}')

def load_database(path,allow_unknown=False,verify_proofs=True):
    d=Database();d.parse_file(path,verify_proofs,allow_unknown);return d

def main():
    if len(sys.argv)<2: print('usage: mmverify_simple.py file.mm');return 2
    try:
        d=load_database(sys.argv[1],allow_unknown=False,verify_proofs=True)
        print(f'OK {d.proof_count} proofs, {d.statement_count} statements')
        return 0
    except Exception as e:
        print('ERROR:',e,file=sys.stderr);return 1
if __name__=='__main__': raise SystemExit(main())
