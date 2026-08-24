#!/usr/bin/env python3
from pathlib import Path
import re,sys,json,traceback

TOK=re.compile(r'\$\(|\$\)|\$\{|\$\}|\$\[|\$\]|\$[cvfedap=.]|\S+')
BASE_NAMES={'52d068cf-64af-4c1e-b9d4-3c54ebc0df12.mm','56475e8c-864a-4be6-ac39-47cb5e00b514.mm','nf.mm'}

class Assertion:
    def __init__(self,label,expr,hyps,dv,kind,file):
        self.label=label;self.expr=tuple(expr);self.hyps=list(hyps);self.dv=set(dv);self.kind=kind;self.file=file

class MM:
    def __init__(self,rootdir):
        self.rootdir=Path(rootdir);self.const=set();self.vars=set();self.labels={};self.scopes=[];self.seen_files=set();self.verified=[];self.trusted=[];self.errors=[]
        self.push_scope()
    def push_scope(self):
        if self.scopes:
            p=self.scopes[-1];self.scopes.append({'f':list(p['f']),'e':list(p['e']),'d':set(p['d'])})
        else:self.scopes.append({'f':[],'e':[],'d':set()})
    def pop_scope(self):self.scopes.pop()
    @property
    def sc(self):return self.scopes[-1]
    def tokenize(self,path):
        s=path.read_text(errors='replace');ts=TOK.findall(s);out=[];i=0
        while i<len(ts):
            if ts[i]=='$(':
                i+=1
                while i<len(ts) and ts[i]!='$)':i+=1
                i+=1;continue
            out.append(ts[i]);i+=1
        return out
    def resolve(self,name,parent):
        p=parent/name
        if p.exists():return p
        p=self.rootdir/name
        if p.exists():return p
        # global search
        hits=list(self.rootdir.rglob(name))+list(Path('/mnt/data').rglob(name))
        return hits[0] if hits else p
    def mandatory(self,expr):
        # all variables in conclusion and active essential hyps
        used={t for t in expr if t in self.vars}
        for _,e in self.sc['e']:used.update(t for t in e if t in self.vars)
        fh=[(lab,e) for lab,e in self.sc['f'] if len(e)>=2 and e[1] in used]
        return fh+list(self.sc['e'])
    def add_assertion(self,label,kind,expr,file):
        hyps=self.mandatory(expr)
        used=set()
        for _,e in hyps:used.update(t for t in e if t in self.vars)
        used.update(t for t in expr if t in self.vars)
        dv={(a,b) if a<b else (b,a) for a,b in self.sc['d'] if a in used and b in used}
        a=Assertion(label,expr,hyps,dv,kind,str(file));self.labels[label]=a;return a
    def subst_expr(self,expr,sub):
        out=[]
        for t in expr:out.extend(sub.get(t,(t,)))
        return tuple(out)
    def verify_proof(self,ass,proof,current_d):
        if not proof:raise ValueError('empty proof')
        steps=[]
        if proof[0]=='(':
            try: close=proof.index(')')
            except ValueError: raise ValueError('unterminated compressed label list')
            refs=[lab for lab,_ in ass.hyps]+proof[1:close]
            acc=0
            for char in ''.join(proof[close+1:]):
                if 'U'<=char<='Y':
                    acc=acc*5+(ord(char)-ord('U')+1)
                elif 'A'<=char<='T':
                    number=acc*20+(ord(char)-ord('A')+1);acc=0
                    if number<=len(refs):steps.append(('label',refs[number-1]))
                    else:steps.append(('saved',number-len(refs)-1))
                elif char=='Z':
                    if acc:raise ValueError('unfinished compressed number before Z')
                    steps.append(('save',None))
                elif char=='?':raise ValueError('unknown compressed proof step')
                else:raise ValueError(f'invalid compressed proof character {char!r}')
            if acc:raise ValueError('unfinished compressed proof number')
        else:
            steps=[('label',tok) for tok in proof]
        stack=[]
        saved=[]
        for kind,value in steps:
            if kind=='save':
                if not stack:raise ValueError('save on empty proof stack')
                saved.append(stack[-1]);continue
            if kind=='saved':
                if value<0 or value>=len(saved):raise ValueError(f'bad saved-step reference {value}')
                stack.append(saved[value]);continue
            tok=value
            if tok not in self.labels:raise KeyError(f'unknown proof label {tok}')
            q=self.labels[tok]
            if q.kind in ('$f','$e'):
                stack.append(q.expr);continue
            n=len(q.hyps)
            if len(stack)<n:raise ValueError(f'stack underflow at {tok}')
            args=stack[-n:] if n else []
            if n:
                del stack[-n:]
            sub={}
            # floating hypotheses first
            for (hlab,h),got in zip(q.hyps,args):
                if h and h[0] in ('class','wff','setvar') and len(h)==2 and h[1] in self.vars:
                    if not got or got[0]!=h[0]:raise ValueError(f'type mismatch at {tok}: {h} vs {got}')
                    v=h[1];val=tuple(got[1:])
                    if v in sub and sub[v]!=val:raise ValueError('inconsistent subst')
                    sub[v]=val
            # all hyps exact after subst
            for (hlab,h),got in zip(q.hyps,args):
                want=self.subst_expr(h,sub)
                if tuple(got)!=want:raise ValueError(f'hyp mismatch at {tok}: want {want}, got {got}')
            # DV conditions
            for x,y in q.dv:
                sx={t for t in sub.get(x,(x,)) if t in self.vars}
                sy={t for t in sub.get(y,(y,)) if t in self.vars}
                for u in sx:
                    for v in sy:
                        if u==v:raise ValueError(f'DV collapse at {tok}: {x},{y}->{u}')
                        pair=(u,v) if u<v else (v,u)
                        if pair not in current_d:raise ValueError(f'missing DV {pair} applying {tok}')
            stack.append(self.subst_expr(q.expr,sub))
        if len(stack)!=1:raise ValueError(f'final stack size {len(stack)}')
        if stack[0]!=ass.expr:raise ValueError(f'wrong conclusion: {stack[0]} != {ass.expr}')
    def process(self,path,trust=None):
        path=Path(path).resolve()
        if path in self.seen_files:return
        self.seen_files.add(path)
        isbase=path.name in BASE_NAMES or (trust is True)
        ts=self.tokenize(path);i=0
        while i<len(ts):
            t=ts[i]
            if t=='$[':
                name=ts[i+1];assert ts[i+2]=='$]';i+=3
                q=self.resolve(name,path.parent);self.process(q,trust=(q.name in BASE_NAMES));continue
            if t=='${':self.push_scope();i+=1;continue
            if t=='$}':self.pop_scope();i+=1;continue
            if t in ('$c','$v','$d'):
                kind=t;i+=1;vals=[]
                while ts[i]!='$.':vals.append(ts[i]);i+=1
                i+=1
                if kind=='$c':self.const.update(vals)
                elif kind=='$v':self.vars.update(vals)
                else:
                    for a in range(len(vals)):
                        for b in range(a+1,len(vals)):
                            x,y=vals[a],vals[b];self.sc['d'].add((x,y) if x<y else (y,x))
                continue
            # labeled
            if i+1<len(ts) and ts[i+1] in ('$f','$e','$a','$p'):
                lab=t;kind=ts[i+1];i+=2;expr=[]
                while ts[i] not in ('$=','$.'):expr.append(ts[i]);i+=1
                proof=[]
                if ts[i]=='$=':
                    i+=1
                    while ts[i]!='$.':proof.append(ts[i]);i+=1
                i+=1
                if kind=='$f':
                    a=Assertion(lab,expr,[],set(),kind,str(path));self.labels[lab]=a;self.sc['f'].append((lab,tuple(expr)));continue
                if kind=='$e':
                    a=Assertion(lab,expr,[],set(),kind,str(path));self.labels[lab]=a;self.sc['e'].append((lab,tuple(expr)));continue
                a=self.add_assertion(lab,kind,expr,path)
                if kind=='$p':
                    if isbase:self.trusted.append(lab)
                    else:
                        self.verify_proof(a,proof,set(self.sc['d']));self.verified.append(lab)
                continue
            i+=1

def main():
    if len(sys.argv)<2:print('usage: local_mm_verify.py root.mm [json]');return 2
    p=Path(sys.argv[1]);mm=MM(p.parent)
    rec={'root':str(p),'ok':False}
    try:
        mm.process(p);rec.update(ok=True,verified=len(mm.verified),trusted=len(mm.trusted),last_verified=mm.verified[-20:])
    except Exception as e:
        rec.update(error=repr(e),traceback=traceback.format_exc(),verified=len(mm.verified),last_verified=mm.verified[-20:])
    out=Path(sys.argv[2]) if len(sys.argv)>2 else p.with_suffix('.verify.json');out.write_text(json.dumps(rec,indent=2))
    print(json.dumps(rec));return 0 if rec['ok'] else 1
if __name__=='__main__':raise SystemExit(main())
