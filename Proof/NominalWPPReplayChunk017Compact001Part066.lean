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
import NominalWPPReplayChunk017Compact001Part065

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

noncomputable def g_wppstopgammahwndv
    (C : Class) (F : Class) (hyp_wppstopgammahwndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopgammahwndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) (hyp_wppstopgammahwndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (h))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : k ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammahwndv_1 hyp_wppstopgammahwndv_2
  have p0001 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) p0002 hyp_wppstopgammahwndv_3
  have p0004 :=
    @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0001 dv_cache_0002
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppstopstep F C)
  have p0009 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0007 p0008
  have p0010 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0013 :=
    Nominal.mp p0011 p0012
  exact p0013

#print axioms g_wppstopgammahwndv

end NFChoice.DirectNominalPrf.WPPReplay
