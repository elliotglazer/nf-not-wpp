from pathlib import Path
import importlib.util,sys,re,time
spec=importlib.util.spec_from_file_location('b','/mnt/data/mmproof_builder_current.py')
b=importlib.util.module_from_spec(spec);sys.modules['b']=b;spec.loader.exec_module(b)
pre=Path('/mnt/data/nf_wpp_stage14_map_pre.mm')
db=b.load(pre,verify=True,allow_incomplete=True)
B=b.Builder(db)
def ap(l,s=None,e=None): return B.apply(l,s or {},e or [])
def chk(n,e):
    if tuple(e)!=db.stmts[n].expr:
        raise RuntimeError(f'{n}\n got {e}\nwant {db.stmts[n].expr}')

proofs={}
# ------------------------------------------------------------------
# KQRel sethood.
# ------------------------------------------------------------------
H=db.stmts['setconslem5'].expr[1:-2]
outer1=('(','_V','X._k','_V',')')
outer2=('(',)+outer1+('X._k','_V',')')
cnvH=("`'_k",)+H
inter=('(',)+outer2+('i^i',)+cnvH+(')',)
img=('(',)+inter+('"_k','A',')')
lhs=('U.1','U.1')+img
absrel=('{','<.','x',',','y','>.','|','<<','x',',','y','>>','e.','A','}')
# Sanity check against setconslem4.
e4=db.stmts['setconslem4'].expr
assert e4[1:233]==lhs and e4[234:]==absrel
p_v=['vvex']
p_xp1,_=ap('xpkex',{'A':('_V',),'B':('_V',)},[p_v,p_v])
p_xp2,_=ap('xpkex',{'A':outer1,'B':('_V',)},[p_xp1,p_v])
p_h=['setconslem5']
# Seed syntax proof for the giant H expression from the actual syntax prefix of
# setconslem5's proof is unnecessary; the recursive syntax builder handles it.
p_cnv,_=ap('cnvkex',{'A':H},[p_h])
p_inter,_=ap('inex',{'A':outer2,'B':cnvH},[p_xp2,p_cnv])
p_img,_=ap('imakex',{'A':inter,'B':('A',)},[p_inter,['kqrelex.1']])
p_u1,_=ap('uni1ex',{'A':img},[p_img])
p_u2,_=ap('uni1ex',{'A':('U.1',)+img},[p_u1])
p_sc4,_=ap('setconslem4',{'A':('A',),'x':('x',),'y':('y',)},[])
p_df,_=ap('df-kqrel',{'A':('A',),'x':('x',),'y':('y',)},[])
p_eq,_=ap('eqtr4i',{'A':('KQRel','A'),'B':absrel,'C':lhs},[p_df,p_sc4])
p_kqex,e=ap('eqeltri',{'A':('KQRel','A'),'B':lhs,'C':('_V',)},[p_eq,p_u2]);chk('kqrelex',e)
proofs['kqrelex']=p_kqex
print('kqrelex',len(p_kqex))

# ------------------------------------------------------------------
# Membership in KQRel.
# ------------------------------------------------------------------
p_df2,_=ap('df-kqrel',{'A':('A',),'x':('x',),'y':('y',)},[])
p_memdef,_=ap('eleq2i',{'A':('KQRel','A'),'B':absrel,'C':('<.','B',',','C','>.')},[p_df2])
# x=B substitution in the QR pair.
p_oq1,_=ap('opkeq1',{'A':('x',),'B':('B',),'C':('y',)},[])
phi=('<<','x',',','y','>>','e.','A')
psi=('<<','B',',','y','>>','e.','A')
ch=('<<','B',',','C','>>','e.','A')
p_sub1,_=ap('eleq1d',{'ph':('x','=','B'),'A':('<<','x',',','y','>>'),'B':('<<','B',',','y','>>'),'C':('A',)},[p_oq1])
p_oq2,_=ap('opkeq2',{'A':('y',),'B':('C',),'C':('B',)},[])
p_sub2,_=ap('eleq1d',{'ph':('y','=','C'),'A':('<<','B',',','y','>>'),'B':('<<','B',',','C','>>'),'C':('A',)},[p_oq2])
p_B=['kqrelbr.1'];p_C=['kqrelbr.2']
p_opab,_=ap('opelopab',{'A':('B',),'B':('C',),'x':('x',),'y':('y',),'ph':phi,'ps':psi,'ch':ch},[p_B,p_C,p_sub1,p_sub2])
w0=('<.','B',',','C','>.','e.','KQRel','A')
w1=('<.','B',',','C','>.','e.')+absrel
p_kqbr,e=ap('bitri',{'ph':w0,'ps':w1,'ch':ch},[p_memdef,p_opab]);chk('kqrelbr',e)
proofs['kqrelbr']=p_kqbr
print('kqrelbr',len(p_kqbr))

# ------------------------------------------------------------------
# FDMinValP sethood and membership.
# ------------------------------------------------------------------
S=('(',"`'_k",'FDMinSep','(','R',',','A',',','B',')','"_k','{','C','}',')')
p_syn_img=['cA','cB','cR','cfdminsep','ccnvk','cC','csn','cimak']
p_syn_val=p_syn_img+['cuni1']
B.memo[('class',)+S]=p_syn_img
B.memo[('class','U.1')+S]=p_syn_val
r=['fdminvalpex.1'];a=['fdminvalpex.2'];b0=['fdminvalpex.3']
p_min,_=ap('fdminsepex',{'R':('R',),'A':('A',),'B':('B',)},[r,a,b0])
p_cnv2,_=ap('cnvkex',{'A':('FDMinSep','(','R',',','A',',','B',')')},[p_min])
p_snC,_=ap('snex',{'A':('C',)},[])
p_img2,_=ap('imakex',{'A':("`'_k",'FDMinSep','(','R',',','A',',','B',')'),'B':('{','C','}')},[p_cnv2,p_snC])
p_uni2,_=ap('uni1ex',{'A':S},[p_img2])
p_dfv,_=ap('df-fdminvalp',{'R':('R',),'A':('A',),'B':('B',),'C':('C',)},[])
p_vex,e=ap('eqeltri',{'A':('FDMinValP','(','R',',','A',',','B',',','C',')'),'B':('U.1',)+S,'C':('_V',)},[p_dfv,p_uni2]);chk('fdminvalpex',e)
proofs['fdminvalpex']=p_vex
print('fdminvalpex',len(p_vex))

p_z=['vz','vex'];p_snz,_=ap('snex',{'A':('z',)},[])
p_defbr,_=ap('eleq2i',{'A':('FDMinValP','(','R',',','A',',','B',',','C',')'),'B':('U.1',)+S,'C':('z',)},[p_dfv])
p_u,_=ap('eluni1',{'A':('z',),'B':S},[p_z])
p_im,_=ap('elimaksn',{'A':("`'_k",'FDMinSep','(','R',',','A',',','B',')'),'B':('C',),'C':('{','z','}')},[p_C,p_snz])
p_cnvbr,_=ap('opkelcnvk',{'A':('C',),'B':('{','z','}'),'C':('FDMinSep','(','R',',','A',',','B',')')},[p_C,p_snz])
w0=('z','e.','FDMinValP','(','R',',','A',',','B',',','C',')')
w1=('z','e.','U.1')+S
w2=('{','z','}','e.')+S
w3=('<<','C',',','{','z','}','>>','e.',"`'_k",'FDMinSep','(','R',',','A',',','B',')')
w4=('<<','{','z','}',',','C','>>','e.','FDMinSep','(','R',',','A',',','B',')')
p01,_=ap('bitri',{'ph':w0,'ps':w1,'ch':w2},[p_defbr,p_u])
p012,_=ap('bitri',{'ph':w0,'ps':w2,'ch':w3},[p01,p_im])
p_valbr,e=ap('bitri',{'ph':w0,'ps':w3,'ch':w4},[p012,p_cnvbr]);chk('fdminvalpbr',e)
proofs['fdminvalpbr']=p_valbr
print('fdminvalpbr',len(p_valbr))

# ------------------------------------------------------------------
# FDMinQ sethood and membership.
# ------------------------------------------------------------------
rq=['fdminqex.1'];aq=['fdminqex.2'];bq=['fdminqex.3']
p_minqset,_=ap('fdminsepex',{'R':('R',),'A':('A',),'B':('B',)},[rq,aq,bq])
p_kqset,_=ap('kqrelex',{'A':('FDMinSep','(','R',',','A',',','B',')')},[p_minqset])
p_dfq,_=ap('df-fdminq',{'R':('R',),'A':('A',),'B':('B',)},[])
p_qex,e=ap('eqeltri',{'A':('FDMinQ','(','R',',','A',',','B',')'),'B':('KQRel','FDMinSep','(','R',',','A',',','B',')'),'C':('_V',)},[p_dfq,p_kqset]);chk('fdminqex',e)
proofs['fdminqex']=p_qex
print('fdminqex',len(p_qex))

# membership definition
p_qmemdef,_=ap('eleq2i',{'A':('FDMinQ','(','R',',','A',',','B',')'),'B':('KQRel','FDMinSep','(','R',',','A',',','B',')'),'C':('<.','{','z','}',',','p','>.')},[p_dfq])
p_snzq,_=ap('snex',{'A':('z',)},[]); p_p=['vp','vex']
p_kqbr2,_=ap('kqrelbr',{'A':('FDMinSep','(','R',',','A',',','B',')'),'B':('{','z','}'),'C':('p',),'x':('x',),'y':('y',)},[p_snzq,p_p])
p_valp,_=ap('fdminvalpbr',{'R':('R',),'A':('A',),'B':('B',),'C':('p',),'z':('z',)},[])
p_valpr,_=ap('bicomi',{'ph':('z','e.','FDMinValP','(','R',',','A',',','B',',','p',')'),'ps':('<<','{','z','}',',','p','>>','e.','FDMinSep','(','R',',','A',',','B',')')},[p_valp])
wq0=('<.','{','z','}',',','p','>.','e.','FDMinQ','(','R',',','A',',','B',')')
wq1=('<.','{','z','}',',','p','>.','e.','KQRel','FDMinSep','(','R',',','A',',','B',')')
wq2=('<<','{','z','}',',','p','>>','e.','FDMinSep','(','R',',','A',',','B',')')
wq3=('z','e.','FDMinValP','(','R',',','A',',','B',',','p',')')
pq01,_=ap('bitri',{'ph':wq0,'ps':wq1,'ch':wq2},[p_qmemdef,p_kqbr2])
p_qbr,e=ap('bitri',{'ph':wq0,'ps':wq2,'ch':wq3},[pq01,p_valpr]);chk('fdminqbr',e)
proofs['fdminqbr']=p_qbr
print('fdminqbr',len(p_qbr))

# ------------------------------------------------------------------
# Map sethood, functionhood, range, and onto.
# ------------------------------------------------------------------
rh=['fdpivmap2ex.1'];ah=['fdpivmap2ex.2'];bh=['fdpivmap2ex.3']
domain=('(','B','X._k','B',')')
val=('FDMinValP','(','R',',','A',',','B',',','p',')')
mapexpr=('(','p','e.',domain,'|->') # unused compact construction below
# construct exact map tokens manually
maptok=('(','p','e.','(','B','X._k','B',')','|->','FDMinValP','(','R',',','A',',','B',',','p',')',')')
p_dom,_=ap('xpkex',{'A':('B',),'B':('B',)},[bh,bh])
p_rel,_=ap('fdminqex',{'R':('R',),'A':('A',),'B':('B',)},[rh,ah,bh])
p_req,_=ap('releqmpt',{
    'A':domain,
    'R':('FDMinQ','(','R',',','A',',','B',')'),
    'V':val,
    'x':('p',),'y':('z',)
},[p_qbr])
# get Hailperin expression from releqmpt result
reqexpr=db.subst_expr(db.stmts['releqmpt'].expr,{
    'A':domain,'R':('FDMinQ','(','R',',','A',',','B',')'),'V':val,'x':('p',),'y':('z',)
})
eqidx=reqexpr.index('='); hail=reqexpr[1:eqidx]; assert reqexpr[eqidx+1:]==maptok
p_hail,_=ap('mptexlem',{'A':domain,'R':('FDMinQ','(','R',',','A',',','B',')')},[p_dom,p_rel])
p_dfmap,_=ap('df-fdpivmap2',{'R':('R',),'A':('A',),'B':('B',),'p':('p',)},[])
p_mapeq,_=ap('eqtr4i',{'A':('FDPivMap2','(','R',',','A',',','B',')'),'B':maptok,'C':hail},[p_dfmap,p_req])
p_mapex,e=ap('eqeltri',{'A':('FDPivMap2','(','R',',','A',',','B',')'),'B':hail,'C':('_V',)},[p_mapeq,p_hail]);chk('fdpivmap2ex',e)
proofs['fdpivmap2ex']=p_mapex
print('fdpivmap2ex',len(p_mapex))

# Functionality via fnmpti.
p_valset,_=ap('fdminvalpex',{'R':('R',),'A':('A',),'B':('B',),'C':('p',)},[rh,ah,bh])
p_fn,e=ap('fnmpti',{'x':('p',),'A':domain,'B':val,'F':('FDPivMap2','(','R',',','A',',','B',')')},[p_valset,p_dfmap]);chk('fdpivmap2fn',e)
proofs['fdpivmap2fn']=p_fn
print('fdpivmap2fn',len(p_fn))

# Range sethood.
p_rn,_=ap('rnex',{'A':('FDPivMap2','(','R',',','A',',','B',')')},[p_mapex])
p_dfrange,_=ap('df-fdpivrange2',{'R':('R',),'A':('A',),'B':('B',)},[])
p_rngex,e=ap('eqeltri',{'A':('FDPivRange2','(','R',',','A',',','B',')'),'B':('ran','FDPivMap2','(','R',',','A',',','B',')'),'C':('_V',)},[p_dfrange,p_rn]);chk('fdpivrange2ex',e)
proofs['fdpivrange2ex']=p_rngex
print('fdpivrange2ex',len(p_rngex))

# Onto range, then rewrite codomain to FDPivRange2.
p_dffn,_=ap('dffn4',{'F':('FDPivMap2','(','R',',','A',',','B',')'),'A':domain},[])
p_onto_rn,_=ap('mpbi',{
    'ph':('FDPivMap2','(','R',',','A',',','B',')','Fn')+domain,
    'ps':('FDPivMap2','(','R',',','A',',','B',')',':')+domain+('-onto->','ran','FDPivMap2','(','R',',','A',',','B',')')
},[p_fn,p_dffn])
p_rnginv,_=ap('eqcomi',{'A':('FDPivRange2','(','R',',','A',',','B',')'),'B':('ran','FDPivMap2','(','R',',','A',',','B',')')},[p_dfrange])
# Build exact wffs for the codomain rewrite.
wonto1=('FDPivMap2','(','R',',','A',',','B',')',':')+domain+('-onto->','ran','FDPivMap2','(','R',',','A',',','B',')')
wonto2=('FDPivMap2','(','R',',','A',',','B',')',':')+domain+('-onto->','FDPivRange2','(','R',',','A',',','B',')')
eqw=('ran','FDPivMap2','(','R',',','A',',','B',')','=','FDPivRange2','(','R',',','A',',','B',')')
biw=('(',)+wonto1+('<->',)+wonto2+(')',)
p_foeq,_=ap('foeq3',{'A':('ran','FDPivMap2','(','R',',','A',',','B',')'),'B':('FDPivRange2','(','R',',','A',',','B',')'),'C':domain,'F':('FDPivMap2','(','R',',','A',',','B',')')},[])
p_foequiv,_=ap('ax-mp',{'ph':eqw,'ps':biw},[p_rnginv,p_foeq])
p_onto,e=ap('mpbi',{'ph':wonto1,'ps':wonto2},[p_onto_rn,p_foequiv]);chk('fdpivmap2onto',e)
proofs['fdpivmap2onto']=p_onto
print('fdpivmap2onto',len(p_onto))

src=pre.read_text()
for lab,pf in proofs.items():
    pat=re.compile(r'('+re.escape(lab)+r'\s+\$p\s+.*?\$=)\s*\?\s*\$\.',re.S)
    src,n=pat.subn(lambda m:m.group(1)+'\n    '+' '.join(pf)+' $.',src,count=1)
    if n!=1: raise RuntimeError((lab,n))
out=Path('/mnt/data/nf_wpp_stage14_map.mm');out.write_text(src)
print(out)
