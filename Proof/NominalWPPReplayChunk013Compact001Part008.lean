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
import NominalWPPReplayChunk013Compact001Part007

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

noncomputable def g_cnvpprod
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cpprod A B)) (syn_cpprod (syn_ccnv A) (syn_ccnv B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_cnvin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd)))
  have p0001 :=
    @g_cnvco (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st))
  have p0002 :=
    @g_cnvco A (syn_c1st)
  have p0003 :=
    @g_cnvcnv (syn_c1st)
  have p0004 :=
    @g_coeq12i (syn_ccnv (syn_ccom A (syn_c1st))) (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccnv A)) (syn_ccnv (syn_ccnv (syn_c1st))) (syn_c1st) p0002 p0003
  have p0005 :=
    @g_coass (syn_ccnv (syn_c1st)) (syn_ccnv A) (syn_c1st)
  have p0006 :=
    @g_n_3eqtri (syn_ccnv (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st)))) (syn_ccom (syn_ccnv (syn_ccom A (syn_c1st))) (syn_ccnv (syn_ccnv (syn_c1st)))) (syn_ccom (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccnv A)) (syn_c1st)) (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_ccnv A) (syn_c1st))) p0001 p0004 p0005
  have p0007 :=
    @g_cnvco (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd))
  have p0008 :=
    @g_cnvco B (syn_c2nd)
  have p0009 :=
    @g_cnvcnv (syn_c2nd)
  have p0010 :=
    @g_coeq12i (syn_ccnv (syn_ccom B (syn_c2nd))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccnv B)) (syn_ccnv (syn_ccnv (syn_c2nd))) (syn_c2nd) p0008 p0009
  have p0011 :=
    @g_coass (syn_ccnv (syn_c2nd)) (syn_ccnv B) (syn_c2nd)
  have p0012 :=
    @g_n_3eqtri (syn_ccnv (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd)))) (syn_ccom (syn_ccnv (syn_ccom B (syn_c2nd))) (syn_ccnv (syn_ccnv (syn_c2nd)))) (syn_ccom (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccnv B)) (syn_c2nd)) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom (syn_ccnv B) (syn_c2nd))) p0007 p0010 p0011
  have p0013 :=
    @g_ineq12i (syn_ccnv (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st)))) (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_ccnv A) (syn_c1st))) (syn_ccnv (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd)))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom (syn_ccnv B) (syn_c2nd))) p0006 p0012
  have p0014 :=
    @g_eqtri (syn_ccnv (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd))))) (syn_cin (syn_ccnv (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st)))) (syn_ccnv (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd))))) (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_ccnv A) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom (syn_ccnv B) (syn_c2nd)))) p0000 p0013
  have p0015 :=
    (by simpa [syn_cpprod] using (Nominal.classEqRefl (syn_cpprod A B)))
  have p0016 :=
    (by simpa [syn_ctxp] using (Nominal.classEqRefl (syn_ctxp (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd)))))
  have p0017 :=
    @g_eqtri (syn_cpprod A B) (syn_ctxp (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd))) (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd)))) p0015 p0016
  have p0018 :=
    @g_cnveqi (syn_cpprod A B) (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd)))) p0017
  have p0019 :=
    (by simpa [syn_cpprod] using (Nominal.classEqRefl (syn_cpprod (syn_ccnv A) (syn_ccnv B))))
  have p0020 :=
    (by simpa [syn_ctxp] using (Nominal.classEqRefl (syn_ctxp (syn_ccom (syn_ccnv A) (syn_c1st)) (syn_ccom (syn_ccnv B) (syn_c2nd)))))
  have p0021 :=
    @g_eqtri (syn_cpprod (syn_ccnv A) (syn_ccnv B)) (syn_ctxp (syn_ccom (syn_ccnv A) (syn_c1st)) (syn_ccom (syn_ccnv B) (syn_c2nd))) (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_ccnv A) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom (syn_ccnv B) (syn_c2nd)))) p0019 p0020
  have p0022 :=
    @g_n_3eqtr4i (syn_ccnv (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd))))) (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_ccnv A) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom (syn_ccnv B) (syn_c2nd)))) (syn_ccnv (syn_cpprod A B)) (syn_cpprod (syn_ccnv A) (syn_ccnv B)) p0014 p0018 p0021
  exact p0022

noncomputable def g_rnpprod
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_crn (syn_cpprod A B)) (syn_cxp (syn_crn A) (syn_crn B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_cnvpprod A B
  have p0001 :=
    @g_dmeqi (syn_ccnv (syn_cpprod A B)) (syn_cpprod (syn_ccnv A) (syn_ccnv B)) p0000
  have p0002 :=
    @g_dmpprod (syn_ccnv A) (syn_ccnv B)
  have p0003 :=
    @g_eqtri (syn_cdm (syn_ccnv (syn_cpprod A B))) (syn_cdm (syn_cpprod (syn_ccnv A) (syn_ccnv B))) (syn_cxp (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B))) p0001 p0002
  have p0004 :=
    @g_dfrn4 (syn_cpprod A B)
  have p0005 :=
    @g_dfrn4 A
  have p0006 :=
    @g_dfrn4 B
  have p0007 :=
    @g_xpeq12i (syn_crn A) (syn_cdm (syn_ccnv A)) (syn_crn B) (syn_cdm (syn_ccnv B)) p0005 p0006
  have p0008 :=
    @g_n_3eqtr4i (syn_cdm (syn_ccnv (syn_cpprod A B))) (syn_cxp (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B))) (syn_crn (syn_cpprod A B)) (syn_cxp (syn_crn A) (syn_crn B)) p0003 p0004 p0007
  exact p0008

#print axioms g_rnpprod

end NFChoice.DirectNominalPrf.WPPReplay
