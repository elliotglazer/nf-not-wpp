from pathlib import Path
import importlib.util,sys
spec=importlib.util.spec_from_file_location(
    'mmvcur', str(Path(__file__).with_name('mmverify_simple.py')))
mmv=importlib.util.module_from_spec(spec);sys.modules['mmvcur']=mmv;spec.loader.exec_module(mmv)

class StmtView:
    def __init__(self,obj):
        self.label=obj.label; self.kind=obj.kind; self.expr=obj.expr
        self.mand_hyps=getattr(obj,'hyps',())
        self.mand_dv=getattr(obj,'dv',())

class DBView:
    def __init__(self,db):
        self.raw=db; self.vars=db.variables
        self.stmts={lab:StmtView(obj) for lab,obj in db.labels.items()}
        self.var_f={}
        for lab,obj in db.hyps.items():
            if obj.kind=='$f' and obj.var is not None:
                self.var_f[obj.var]=lab
    def subst_expr(self,expr,subst):
        return mmv.Database().subst_expr(tuple(expr),subst) if False else tuple(t for x in expr for t in (subst.get(x,(x,)) if x in self.vars else (x,)))

class Builder:
    def __init__(self, db):
        self.db=db
        self.rules_by_type={}
        for st in db.stmts.values():
            if st.kind=='$a' and st.expr and st.expr[0] != '|-':
                self.rules_by_type.setdefault(st.expr[0],[]).append(st)
        self.memo={}; self.inprogress=set()
    def syntax_proof(self,target):
        target=tuple(target)
        if target in self.memo:return self.memo[target]
        if target in self.inprogress:return None
        if len(target)<2:self.memo[target]=None;return None
        tp=target[0];body=target[1:]
        if len(body)==1 and body[0] in self.db.vars:
            lab=self.db.var_f.get(body[0])
            if lab and self.db.stmts[lab].expr[0]==tp:
                self.memo[target]=[lab];return [lab]
        self.inprogress.add(target)
        try:
            for st in self.rules_by_type.get(tp,[]):
                patt=st.expr[1:];vtypes={}
                for hl in st.mand_hyps:
                    h=self.db.stmts[hl]
                    if h.kind=='$f':vtypes[h.expr[1]]=h.expr[0]
                ans=self._match_rule(patt,body,0,0,vtypes,{}, {}, {})
                if ans is None:continue
                subst,subproof=ans;proof=[];ok=True
                for hl in st.mand_hyps:
                    h=self.db.stmts[hl]
                    if h.kind!='$f':ok=False;break
                    var=h.expr[1];hp=subproof.get(var)
                    if hp is None:
                        seg=subst.get(var)
                        if seg is None:ok=False;break
                        hp=self.syntax_proof((h.expr[0],)+seg)
                    if hp is None:ok=False;break
                    proof+=hp
                if ok:
                    proof.append(st.label);self.memo[target]=proof;return proof
            self.memo[target]=None;return None
        finally:self.inprogress.discard(target)
    def _match_rule(self,patt,body,i,j,vtypes,subst,subproof,memo):
        key=(i,j,tuple(sorted(subst.items())))
        if key in memo:return memo[key]
        if i==len(patt):
            r=(dict(subst),dict(subproof)) if j==len(body) else None;memo[key]=r;return r
        if j>len(body):memo[key]=None;return None
        p=patt[i]
        if p not in vtypes:
            if j<len(body) and body[j]==p:
                r=self._match_rule(patt,body,i+1,j+1,vtypes,subst,subproof,memo);memo[key]=r;return r
            memo[key]=None;return None
        if p in subst:
            seg=subst[p]
            if tuple(body[j:j+len(seg)])==seg:
                r=self._match_rule(patt,body,i+1,j+len(seg),vtypes,subst,subproof,memo);memo[key]=r;return r
            memo[key]=None;return None
        minrem=sum(1 for q in patt[i+1:] if q not in vtypes);maxk=len(body)-minrem
        cand=range(j+1,maxk+1)
        if i+1<len(patt) and patt[i+1] not in vtypes:
            lit=patt[i+1];cand=[k for k in cand if k<len(body) and body[k]==lit]
        typ=vtypes[p]
        for k in cand:
            seg=tuple(body[j:k]);hp=self.syntax_proof((typ,)+seg)
            if hp is None:continue
            ns=dict(subst);ns[p]=seg;np=dict(subproof);np[p]=hp
            r=self._match_rule(patt,body,i+1,k,vtypes,ns,np,memo)
            if r is not None:memo[key]=r;return r
        memo[key]=None;return None
    def apply(self,label,subst,essential_seqs):
        st=self.db.stmts[label];proof=[];it=iter(essential_seqs)
        for hl in st.mand_hyps:
            h=self.db.stmts[hl]
            if h.kind=='$f':
                want=self.db.subst_expr(h.expr,subst);hp=self.syntax_proof(want)
                if hp is None:raise ValueError(f'no syntax proof {want} for {label}/{hl}')
                proof+=hp
            else:proof+=next(it)
        proof.append(label)
        return proof,self.db.subst_expr(st.expr,subst)

def load(path,verify=True,allow_incomplete=False):
    raw=mmv.load_database(path,allow_unknown=allow_incomplete,verify_proofs=verify)
    return DBView(raw)
