import WPPCompactSourceSyntax
import WPPCompactSyntaxFVExplicit
import CompactSyntaxFV
import CoreFVSimp
import NominalSubstitutionLemmas
import NominalDefinitionRefl
import NominalDfEu
import NominalAlphaRepairedDfNfc001
import NominalAlphaRepairedBase001003V
import NominalAlphaRepairedBase001004Csb
import NominalAlphaRepairedBase001005Nin
import NominalAlphaRepairedBase001006If
import NominalAlphaRepairedBase001007Pw
import NominalAlphaRepairedBase001008Sn
import NominalAlphaRepairedBase001009Uni
import NominalAlphaRepairedBase001010Int
import NominalAlphaRepairedBase001011Iun
import NominalAlphaRepairedBase001012Leaf1c
import NominalAlphaRepairedBase001013Xpk
import NominalAlphaRepairedBase001014Cnvk
import NominalAlphaRepairedBase001015Ins2k
import NominalAlphaRepairedBase001016Ins3k
import NominalAlphaRepairedBase001017Imak
import NominalAlphaRepairedBase001018P6
import NominalAlphaRepairedBase001019Sik
import NominalAlphaRepairedBase001020Ssetk
import NominalAlphaRepairedBase001021Idk
import NominalAlphaRepairedBase001022Iota
import NominalAlphaRepairedBase001023Addc
import NominalAlphaRepairedBase001024Nnc
import NominalAlphaRepairedBase001025Lefin
import NominalAlphaRepairedBase001026Ltfin
import NominalAlphaRepairedBase001027Ncfin
import NominalAlphaRepairedBase001028Tfin
import NominalAlphaRepairedBase001029Evenfin
import NominalAlphaRepairedBase001030Oddfin
import NominalAlphaRepairedBase001031Sfin
import NominalAlphaRepairedBase001032Spfin
import NominalAlphaRepairedBase001033Phi
import NominalAlphaRepairedBase001034OpReflected001
import NominalAlphaRepairedBase001035Proj1Reflected001
import NominalAlphaRepairedBase001036Proj2Reflected001
import NominalAlphaRepairedBase001037OpabOpaqueHoisted004
import NominalAlphaRepairedBase001038Leaf1stReflected001
import NominalAlphaRepairedBase001039SwapReflected001
import NominalAlphaRepairedBase001040SsetReflected001
import NominalAlphaRepairedBase001041CoReflected001
import NominalAlphaRepairedBase001042ImaReflected001
import NominalAlphaRepairedBase001043SiReflected001
import NominalAlphaRepairedBase001044IdReflected001
import NominalAlphaRepairedBase001045XpReflected001
import NominalAlphaRepairedBase001046CnvReflected001
import NominalAlphaRepairedBase001047FvReflected001
import NominalAlphaRepairedBase001048Leaf2ndReflected001
import NominalAlphaRepairedBase001049OprabReflected001
import NominalAlphaPrefix050WppNotmem014Data
import NominalAlphaGlobal051ProofData001
import NominalAlphaRelease004Coarse052
import NominalAlphaRelease004Coarse053
import NominalAlphaRelease004Coarse054
import NominalAlphaRelease004Coarse055
import NominalAlphaRelease004Coarse056
import NominalAlphaRelease004Coarse057
import NominalAlphaRelease004Coarse058
import NominalAlphaRelease004Coarse059
import NominalAlphaRelease004Coarse060
import NominalAlphaRelease004Coarse061
import NominalAlphaRelease004Coarse062
import NominalAlphaRelease004Coarse063
import NominalAlphaRelease004Coarse064
import NominalAlphaRelease004Coarse065
import NominalAlphaRelease004Coarse066
import NominalAlphaRelease004Coarse067
import NominalAlphaRelease004Coarse068
import NominalAlphaRelease004Coarse069
import NominalAlphaRelease004Coarse070
import NominalAlphaRelease004Coarse071
import NominalAlphaRelease004Coarse072
import NominalAlphaRelease004Coarse073
import NominalAlphaRelease004Coarse074
import NominalAlphaRelease004Coarse075
import NominalAlphaRelease004Coarse076
import NominalAlphaRelease004Coarse077
import NominalAlphaRelease004Coarse078
import NominalAlphaRelease004Coarse079
import NominalAlphaRelease004Coarse080
import NominalAlphaRelease004Coarse081
import NominalAlphaRelease004Coarse082
import NominalAlphaRelease004Coarse083
import NominalAlphaRelease004Coarse084
import NominalAlphaRelease004Coarse085
import NominalAlphaRelease004Coarse086
import NominalAlphaRelease004Coarse087
import NominalAlphaHygieneV5Probe088
import NominalAlphaRelease004Coarse089
import NominalAlphaRelease004Coarse090
import NominalAlphaHygieneV5Coalesced091B
import NominalAlphaHygieneV5Coalesced092
import NominalAlphaHygieneV5Coalesced093
import NominalAlphaHygieneV5Coalesced094
import NominalAlphaHygieneV5Coalesced095
import NominalAlphaHygieneV5Coalesced096
import NominalAlphaHygieneV5Coalesced097
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk017Compact001Part025

set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

noncomputable def g_hnwcutcodenestndv
    (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_chnwcutcode (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv x)) (syn_chnwcutcode R D (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv x))))
  have p0001 :=
    @g_a1i (.classEq (syn_chnwcutcode (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv x)) (syn_cop (syn_cin (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cxp (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0000
  have p0002 :=
    @g_strictsegcut x y D R
  have p0003 :=
    @g_strictsegcut x y D R
  have p0004 :=
    @g_xpeq12d (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0002 p0003
  have p0005 :=
    @g_ineq2 (syn_cxp (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cxp (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classEq (syn_cin (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cxp (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0004 p0005
  have p0007 :=
    @g_strictsegcut x y D R
  have p0008 :=
    @g_inss1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))
  have p0009 :=
    @g_a1i (syn_wss (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0008
  have p0010 :=
    @g_eqsstr3d (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) p0007 p0009
  have p0011 :=
    @g_strictsegrestrnest x y D R
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.classEq (syn_cin (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0010 p0011
  have p0013 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cxp (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0006 p0012
  have p0014 :=
    @g_strictsegcut x y D R
  have p0015 :=
    @g_opeq12d (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cxp (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0013 p0014
  have p0016 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x))))
  have p0017 :=
    @g_a1i (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0016
  have p0018 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0017
  have p0019 :=
    @g_n_3eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_chnwcutcode (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv x)) (syn_cop (syn_cin (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cxp (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x))))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chnwcutcode R D (.cv x)) p0001 p0015 p0018
  exact p0019

noncomputable def g_hnwcutcodeeq12ndv
    (x : Var) (D : Class) (R : Class) (S : Class) (E : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq R S) (.classEq D E)) (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode S E (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  have p0000 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x))))
  have p0001 :=
    @g_a1i (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classEq R S) (.classEq D E)) p0000
  have p0002 :=
    @g_simpl (.classEq R S) (.classEq D E)
  have p0003 :=
    @g_simpr (.classEq R S) (.classEq D E)
  have p0004 :=
    @g_simpl (.classEq R S) (.classEq D E)
  have p0005 :=
    @g_difeq1d (syn_wa (.classEq R S) (.classEq D E)) R S (syn_cid) p0004
  have p0006 :=
    @g_cnveqd (syn_wa (.classEq R S) (.classEq D E)) (syn_cdif R (syn_cid)) (syn_cdif S (syn_cid)) p0005
  have p0007 :=
    @g_imaeq1d (syn_wa (.classEq R S) (.classEq D E)) (syn_ccnv (syn_cdif R (syn_cid))) (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)) p0006
  have p0008 :=
    @g_ineq12d (syn_wa (.classEq R S) (.classEq D E)) D E (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) p0003 p0007
  have p0009 :=
    @g_simpr (.classEq R S) (.classEq D E)
  have p0010 :=
    @g_simpl (.classEq R S) (.classEq D E)
  have p0011 :=
    @g_difeq1d (syn_wa (.classEq R S) (.classEq D E)) R S (syn_cid) p0010
  have p0012 :=
    @g_cnveqd (syn_wa (.classEq R S) (.classEq D E)) (syn_cdif R (syn_cid)) (syn_cdif S (syn_cid)) p0011
  have p0013 :=
    @g_imaeq1d (syn_wa (.classEq R S) (.classEq D E)) (syn_ccnv (syn_cdif R (syn_cid))) (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)) p0012
  have p0014 :=
    @g_ineq12d (syn_wa (.classEq R S) (.classEq D E)) D E (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) p0009 p0013
  have p0015 :=
    @g_xpeq12d (syn_wa (.classEq R S) (.classEq D E)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) p0008 p0014
  have p0016 :=
    @g_ineq12d (syn_wa (.classEq R S) (.classEq D E)) R S (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) p0002 p0015
  have p0017 :=
    @g_simpr (.classEq R S) (.classEq D E)
  have p0018 :=
    @g_simpl (.classEq R S) (.classEq D E)
  have p0019 :=
    @g_difeq1d (syn_wa (.classEq R S) (.classEq D E)) R S (syn_cid) p0018
  have p0020 :=
    @g_cnveqd (syn_wa (.classEq R S) (.classEq D E)) (syn_cdif R (syn_cid)) (syn_cdif S (syn_cid)) p0019
  have p0021 :=
    @g_imaeq1d (syn_wa (.classEq R S) (.classEq D E)) (syn_ccnv (syn_cdif R (syn_cid))) (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)) p0020
  have p0022 :=
    @g_ineq12d (syn_wa (.classEq R S) (.classEq D E)) D E (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) p0017 p0021
  have p0023 :=
    @g_opeq12d (syn_wa (.classEq R S) (.classEq D E)) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) p0016 p0022
  have p0024 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode S E (.cv x))))
  have p0025 :=
    @g_a1i (.classEq (syn_chnwcutcode S E (.cv x)) (syn_cop (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classEq R S) (.classEq D E)) p0024
  have p0026 :=
    @g_eqcomd (syn_wa (.classEq R S) (.classEq D E)) (syn_chnwcutcode S E (.cv x)) (syn_cop (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) p0025
  have p0027 :=
    @g_n_3eqtrd (syn_wa (.classEq R S) (.classEq D E)) (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cop (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))) (syn_chnwcutcode S E (.cv x)) p0001 p0023 p0026
  exact p0027

noncomputable def g_hnwcutcodeambientndv
    (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0001 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0002 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0003 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0001 p0002
  have p0004 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c2nd) p0003
  have p0005 :=
    @g_eleq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u)) (.cv x) p0004
  have p0006 :=
    @g_mpbird (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0000 p0005
  have p0007 :=
    @g_hncodetotalleftmemndv u A dv_cache_0001
  have p0008 :=
    @g_hwcnweclndv A (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_hnwcutcodecnclndv (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) p0009
  have p0011 :=
    @g_hncodetotalleftmemndv u A dv_cache_0001
  have p0012 :=
    @g_hwcnbaseclndv A (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_hwcnssbase A (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) p0013
  have p0015 :=
    @g_ssel (syn_chwcn (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_chwcn A) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_syl (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x)) (syn_chwcn (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x)) (syn_chwcn A)) p0010 p0016
  have p0018 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x)) (syn_chwcn A)) p0006 p0017
  have p0019 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0020 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0021 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0019 p0020
  have p0022 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c1st) p0021
  have p0023 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0024 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0025 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u)) p0023 p0024
  have p0026 :=
    @g_fveq2d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (.cv u) (syn_c2nd) p0025
  have p0027 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u))) (.classEq (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u))) p0022 p0026
  have p0028 :=
    @g_hnwcutcodeeq12ndv x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
  have p0029 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (.cv u))) (.classEq (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) p0027 p0028
  have p0030 :=
    @g_eleq1d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A) p0029
  have p0031 :=
    @g_mpbid (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.cv x)) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0018 p0030
  exact p0031

#print axioms g_hnwcutcodeambientndv

end NFChoice.DirectNominalPrf.WPPReplay
