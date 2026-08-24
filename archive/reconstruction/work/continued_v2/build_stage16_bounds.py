from pathlib import Path
import importlib.util,sys,re
spec=importlib.util.spec_from_file_location('b','/mnt/data/mmproof_builder_current.py')
b=importlib.util.module_from_spec(spec);sys.modules['b']=b;spec.loader.exec_module(b)
pre=Path('/mnt/data/nf_wpp_stage16_bounds_pre.mm')
db=b.load(pre,verify=True,allow_incomplete=True); B=b.Builder(db)
def ap(l,s=None,e=None): return B.apply(l,s or {},e or [])
def chk(n,e):
    if tuple(e)!=db.stmts[n].expr: raise RuntimeError(f'{n}\n got {e}\nwant {db.stmts[n].expr}')
P={}
D=('FDDom','(','A',',','B',')')
E0=('FDE0','(','A',',','B',')'); E1=('FDE1','(','A',',','B',')')
SEP=('FDSep','(','A',',','B',')'); NON=('FDNonMin','(','R',',','A',',','B',')')
MIN=('FDMinSep','(','R',',','A',',','B',')')
raw0=('(','(','FDPrj0','o._k','FDMem',')','i^i')+D+(')',)
raw1=('(','(','FDPrj1','o._k','FDMem',')','i^i')+D+(')',)
# E0,E1 subset domain.
p_in0,_=ap('inss2',{'A':('(','FDPrj0','o._k','FDMem',')'),'B':D},[])
p_df0,_=ap('df-fde0',{'A':('A',),'B':('B',)},[])
P['fde0ssdom'],e=ap('eqsstri',{'A':E0,'B':raw0,'C':D},[p_df0,p_in0]);chk('fde0ssdom',e)
p_in1,_=ap('inss2',{'A':('(','FDPrj1','o._k','FDMem',')'),'B':D},[])
p_df1,_=ap('df-fde1',{'A':('A',),'B':('B',)},[])
P['fde1ssdom'],e=ap('eqsstri',{'A':E1,'B':raw1,'C':D},[p_df1,p_in1]);chk('fde1ssdom',e)
# Symmetric difference subset domain.
d01=('(',)+E0+('\\',)+E1+(')',); d10=('(',)+E1+('\\',)+E0+(')',); un=('(',)+d01+('u.',)+d10+(')',)
p_d0,_=ap('difss',{'A':E0,'B':E1},[]); p_c0,_=ap('sstri',{'A':d01,'B':E0,'C':D},[p_d0,P['fde0ssdom']])
p_d1,_=ap('difss',{'A':E1,'B':E0},[]); p_c1,_=ap('sstri',{'A':d10,'B':E1,'C':D},[p_d1,P['fde1ssdom']])
p_un,_=ap('unssi',{'A':d01,'B':d10,'C':D},[p_c0,p_c1])
p_sym,_=ap('df-symdif',{'A':E0,'B':E1},[])
p_dfsep,_=ap('df-fdsep',{'A':('A',),'B':('B',)},[])
sym=('(',)+E0+('(+) ',) if False else ('(',)+E0+('(+)',)+E1+(')',)
p_eqsep,_=ap('eqtri',{'A':SEP,'B':sym,'C':un},[p_dfsep,p_sym])
P['fdsepssdom'],e=ap('eqsstri',{'A':SEP,'B':un,'C':D},[p_eqsep,p_un]);chk('fdsepssdom',e)
# Minimum separators subset domain.
rawmin=('(',)+SEP+('\\',)+NON+(')',)
p_dif,_=ap('difss',{'A':SEP,'B':NON},[])
p_dfmin,_=ap('df-fdminsep',{'R':('R',),'A':('A',),'B':('B',)},[])
p_minsep,_=ap('eqsstri',{'A':MIN,'B':rawmin,'C':SEP},[p_dfmin,p_dif])
P['fdminsepssdom'],e=ap('sstri',{'A':MIN,'B':SEP,'C':D},[p_minsep,P['fdsepssdom']]);chk('fdminsepssdom',e)
# Every value is a subset of A.
Cset=['fdminvalpss.1']; zset=['vz','vex']; snz,_=ap('snex',{'A':('z',)},[])
VAL=('FDMinValP','(','R',',','A',',','B',',','C',')')
p_vbr,_=ap('fdminvalpbr',{'R':('R',),'A':('A',),'B':('B',),'C':('C',),'z':('z',)},[])
rel=('<<','{','z','}',',','C','>>','e.')+MIN
vcel=('z','e.')+VAL
p_vrel,_=ap('biimpi',{'ph':vcel,'ps':rel},[p_vbr])
p_mindom,_=ap('sseli',{'A':MIN,'B':D,'C':('<<','{','z','}',',','C','>>')},[P['fdminsepssdom']])
p_vdom,_=ap('syl',{'ph':vcel,'ps':rel,'ch':('<<','{','z','}',',','C','>>','e.')+D},[p_vrel,p_mindom])
rawdom=('(','~P1','A','X._k','(','B','X._k','B',')',')')
p_dfdom,_=ap('df-fddom',{'A':('A',),'B':('B',)},[])
p_domdef,_=ap('eleq2i',{'A':D,'B':rawdom,'C':('<<','{','z','}',',','C','>>')},[p_dfdom])
p_op,_=ap('opkelxpk',{'A':('{','z','}'),'B':('C',),'C':('~P1','A'),'D':('(','B','X._k','B',')')},[snz,Cset])
rawmem=('<<','{','z','}',',','C','>>','e.')+rawdom
conj=('(','{','z','}','e.','~P1','A','/\\','C','e.','(','B','X._k','B',')',')')
p_domconj,_=ap('bitri',{'ph':('<<','{','z','}',',','C','>>','e.')+D,'ps':rawmem,'ch':conj},[p_domdef,p_op])
p_left,_=ap('simplbi',{'ph':('<<','{','z','}',',','C','>>','e.')+D,'ps':('{','z','}','e.','~P1','A'),'ch':('C','e.','(','B','X._k','B',')')},[p_domconj])
p_sn,_=ap('snelpw1',{'A':('z',),'B':('A',)},[])
p_snimp,_=ap('biimpi',{'ph':('{','z','}','e.','~P1','A'),'ps':('z','e.','A')},[p_sn])
p_toA,_=ap('3syl',{'ph':vcel,'ps':('<<','{','z','}',',','C','>>','e.')+D,'ch':('{','z','}','e.','~P1','A'),'th':('z','e.','A')},[p_vdom,p_left,p_snimp])
P['fdminvalpss'],e=ap('ssriv',{'x':('z',),'A':VAL,'B':('A',)},[p_toA]);chk('fdminvalpss',e)
# Range subset power set of A.
r=['fdpivrange2sspw.1'];a=['fdpivrange2sspw.2'];bb=['fdpivrange2sspw.3']
RNG=('FDPivRange2','(','R',',','A',',','B',')'); D2=('(','B','X._k','B',')')
VALP=('FDMinValP','(','R',',','A',',','B',',','p',')')
# For a witness p, equality of its value with C implies C subset A.
p_pset=['vp','vex']
p_valss,_=ap('fdminvalpss',{'R':('R',),'A':('A',),'B':('B',),'C':('p',),'z':('z',)},[p_pset])
eqw=VALP+('=','c'); valss=VALP+('C_','A'); css=('c','C_','A')
p_valssa,_=ap('a1i',{'ph':valss,'ps':eqw},[p_valss])
p_sseq,_=ap('sseq1',{'A':VALP,'B':('c',),'C':('A',)},[])
p_bided,_=ap('mpbid',{'ph':eqw,'ps':valss,'ch':css},[p_valssa,p_sseq])
# Eliminate the restricted existential.
rex=('E.','p','e.')+D2+eqw
p_rexlim,_=ap('rexlimivw',{'x':('p',),'A':D2,'ph':eqw,'ps':css},[p_bided])
p_rngbr,_=ap('fdpivrange2br',{'R':('R',),'A':('A',),'B':('B',),'C':('c',),'p':('p',)},[r,a,bb])
p_rngrex,_=ap('biimpi',{'ph':('c','e.')+RNG,'ps':rex},[p_rngbr])
p_rngss,_=ap('syl',{'ph':('c','e.')+RNG,'ps':rex,'ch':css},[p_rngrex,p_rexlim])
# Convert subsethood to power-set membership.
p_Cset=['vc','vex']
p_elpwg,_=ap('elpwg',{'A':('c',),'B':('A',),'V':('_V',)},[])
p_elp,_=ap('ax-mp',{'ph':('c','e.','_V'),'ps':('(','c','e.','~P','A','<->','c','C_','A',')')},[p_Cset,p_elpwg])
p_tomem,_=ap('sylibr',{'ph':('c','e.')+RNG,'ps':css,'ch':('c','e.','~P','A')},[p_rngss,p_elp])
P['fdpivrange2sspw'],e=ap('ssriv',{'x':('c',),'A':RNG,'B':('~P','A')},[p_tomem]);chk('fdpivrange2sspw',e)
# Install proofs.
src=pre.read_text()
for lab,pf in P.items():
 pat=re.compile(r'('+re.escape(lab)+r'\s+\$p\s+.*?\$=)\s*\?\s*\$\.',re.S)
 src,n=pat.subn(lambda m:m.group(1)+'\n    '+' '.join(pf)+' $.',src,count=1)
 if n!=1: raise RuntimeError((lab,n))
out=Path('/mnt/data/nf_wpp_stage16_bounds.mm');out.write_text(src);print(out)
