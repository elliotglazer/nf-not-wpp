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
import NominalWPPReplayChunk016Compact001Part023

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

noncomputable def g_wecutisogeneq
    (D : Class) (R : Class) (S : Class) (E : Class) (hyp_wecutisogeneq_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisogeneq_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.classEq (syn_cwecutiso R D S E) (syn_cwecutisogen R D S E)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  have p0000 :=
    @g_wecutisossgen D R S E hyp_wecutisogeneq_1 hyp_wecutisogeneq_2
  have p0001 :=
    @g_wecutisogensswecutiso D R S E hyp_wecutisogeneq_1 hyp_wecutisogeneq_2
  have p0002 :=
    @g_eqssi (syn_cwecutiso R D S E) (syn_cwecutisogen R D S E) p0000 p0001
  exact p0002

noncomputable def g_wecutisogenex
    (D : Class) (R : Class) (S : Class) (E : Class) (hyp_wecutisogenex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisogenex_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.classMem (syn_cwecutisogen R D S E) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  have p0000 :=
    (by simpa [syn_cwecutisogen] using (Nominal.classEqRefl (syn_cwecutisogen R D S E)))
  have p0001 :=
    @g_hwbijex
  have p0002 :=
    @g_vvex
  have p0003 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0001 p0002
  have p0004 :=
    @g_hwgenex
  have p0005 :=
    @g_cnvex (syn_chwgen) p0004
  have p0006 :=
    @g_hnwcutrelex D R hyp_wecutisogenex_1
  have p0007 :=
    @g_rnex (syn_chnwcutrel R D) p0006
  have p0008 :=
    @g_hnwcutrelex E S hyp_wecutisogenex_2
  have p0009 :=
    @g_rnex (syn_chnwcutrel S E) p0008
  have p0010 :=
    @g_xpex (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)) p0007 p0009
  have p0011 :=
    @g_imaex (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))) p0005 p0010
  have p0012 :=
    @g_inex (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) p0003 p0011
  have p0013 :=
    @g_dmex (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) p0012
  have p0014 :=
    @g_eqeltri (syn_cwecutisogen R D S E) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (syn_cvv) p0000 p0013
  exact p0014

noncomputable def g_wecutisoex
    (D : Class) (R : Class) (S : Class) (E : Class) (hyp_wecutisoex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisoex_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.classMem (syn_cwecutiso R D S E) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  have p0000 :=
    @g_wecutisogeneq D R S E hyp_wecutisoex_1 hyp_wecutisoex_2
  have p0001 :=
    @g_wecutisogenex D R S E hyp_wecutisoex_1 hyp_wecutisoex_2
  have p0002 :=
    @g_eqeltri (syn_cwecutiso R D S E) (syn_cwecutisogen R D S E) (syn_cvv) p0000 p0001
  exact p0002

noncomputable def g_wecutisouniex
    (D : Class) (R : Class) (S : Class) (E : Class) (hyp_wecutisouniex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisouniex_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  have p0000 :=
    @g_wecutisoex D R S E hyp_wecutisouniex_1 hyp_wecutisouniex_2
  have p0001 :=
    @g_uniex (syn_cwecutiso R D S E) p0000
  exact p0001

noncomputable def g_wecutcardfnfn
    (D : Class) (R : Class) :
    Nominal.NPrf (syn_wfn (syn_cwecutcardfn R D) (syn_cpw1 (syn_cpw1 D))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ncex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wecutcardfn D R q dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_fnmpti q (syn_cpw1 (syn_cpw1 D)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_cwecutcardfn R D) dv_cache_0003 p0000 p0001
  exact p0002

noncomputable def g_wecutcardfactorex
    (D : Class) (R : Class) (hyp_wecutcardfactorex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_cwecutcardfactor R D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cwecutcardfactor] using (Nominal.classEqRefl (syn_cwecutcardfactor R D)))
  have p0001 :=
    @g_enex
  have p0002 :=
    @g_imageex (syn_cen) p0001
  have p0003 :=
    @g_n_2ndex
  have p0004 :=
    @g_hnwcutrelex D R hyp_wecutcardfactorex_1
  have p0005 :=
    @g_coex (syn_c2nd) (syn_chnwcutrel R D) p0003 p0004
  have p0006 :=
    @g_siex (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) p0005
  have p0007 :=
    @g_coex (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) p0002 p0006
  have p0008 :=
    @g_eqeltri (syn_cwecutcardfactor R D) (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (syn_cvv) p0000 p0007
  exact p0008

noncomputable def g_wecutcardfactorfn
    (D : Class) (R : Class) (hyp_wecutcardfactorfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_cwecutcardfactor R D) (syn_cpw1 (syn_cpw1 D))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_enex
  have p0001 :=
    @g_wppimagefn (syn_cen) p0000
  have p0002 :=
    @g_ssv (syn_crn (syn_cimage (syn_cen)))
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cen)) (syn_cvv)) (syn_wss (syn_crn (syn_cimage (syn_cen))) (syn_cvv)) p0001 p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cimage (syn_cen)) (syn_cvv) (syn_cvv))))
  have p0005 :=
    @g_mpbir (syn_wf (syn_cimage (syn_cen)) (syn_cvv) (syn_cvv)) (syn_wa (syn_wfn (syn_cimage (syn_cen)) (syn_cvv)) (syn_wss (syn_crn (syn_cimage (syn_cen))) (syn_cvv))) p0003 p0004
  have p0006 :=
    @g_n_2ndfo
  have p0007 :=
    @g_fof (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_hnwcutrelfndv D R hyp_wecutcardfactorfn_1
  have p0010 :=
    @g_ssv (syn_chwcn D)
  have p0011 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) (syn_wss (syn_chwcn D) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_cvv) (syn_chnwcutrel R D)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_pm3_2i (syn_wf (syn_c2nd) (syn_cvv) (syn_cvv)) (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_cvv)) p0008 p0013
  have p0015 :=
    @g_fco (syn_cpw1 D) (syn_cvv) (syn_cvv) (syn_c2nd) (syn_chnwcutrel R D)
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_sifmap (syn_cpw1 D) (syn_cvv) (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_ssv (syn_cpw1 (syn_cvv))
  have p0020 :=
    @g_pm3_2i (syn_wf (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_cvv))) (syn_wss (syn_cpw1 (syn_cvv)) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_fss (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_cvv)) (syn_cvv) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i (syn_wf (syn_cimage (syn_cen)) (syn_cvv) (syn_cvv)) (syn_wf (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)) (syn_cvv)) p0005 p0022
  have p0024 :=
    @g_fco (syn_cpw1 (syn_cpw1 D)) (syn_cvv) (syn_cvv) (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_ffn (syn_cpw1 (syn_cpw1 D)) (syn_cvv) (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    (by simpa [syn_cwecutcardfactor] using (Nominal.classEqRefl (syn_cwecutcardfactor R D)))
  have p0029 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 D)) (syn_cwecutcardfactor R D) (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) p0028
  have p0030 :=
    @g_mpbir (syn_wfn (syn_cwecutcardfactor R D) (syn_cpw1 (syn_cpw1 D))) (syn_wfn (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (syn_cpw1 (syn_cpw1 D))) p0027 p0029
  exact p0030

noncomputable def g_wecutcardhrelfn
    (D : Class) (R : Class) (hyp_wecutcardhrelfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_hnwcutrelfndv D R hyp_wecutcardhrelfn_1
  have p0001 :=
    @g_ssv (syn_chwcn D)
  have p0002 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) (syn_wss (syn_chwcn D) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_cvv) (syn_chnwcutrel R D)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_ffn (syn_cpw1 D) (syn_cvv) (syn_chnwcutrel R D)
  have p0006 :=
    Nominal.mp p0004 p0005
  exact p0006

noncomputable def g_wecutcardinnerf
    (D : Class) (R : Class) (hyp_wecutcardinnerf_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) (syn_cpw1 D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_n_2ndfo
  have p0001 :=
    @g_fof (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_hnwcutrelfndv D R hyp_wecutcardinnerf_1
  have p0004 :=
    @g_ssv (syn_chwcn D)
  have p0005 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) (syn_wss (syn_chwcn D) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_cvv) (syn_chnwcutrel R D)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wf (syn_c2nd) (syn_cvv) (syn_cvv)) (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_cvv)) p0002 p0007
  have p0009 :=
    @g_fco (syn_cpw1 D) (syn_cvv) (syn_cvv) (syn_c2nd) (syn_chnwcutrel R D)
  have p0010 :=
    Nominal.mp p0008 p0009
  exact p0010

noncomputable def g_wecutcardsiliftfn
    (D : Class) (R : Class) (hyp_wecutcardsiliftfn_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wfn (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_n_2ndfo
  have p0001 :=
    @g_fof (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_hnwcutrelfndv D R hyp_wecutcardsiliftfn_1
  have p0004 :=
    @g_ssv (syn_chwcn D)
  have p0005 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) (syn_wss (syn_chwcn D) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_cvv) (syn_chnwcutrel R D)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wf (syn_c2nd) (syn_cvv) (syn_cvv)) (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_cvv)) p0002 p0007
  have p0009 :=
    @g_fco (syn_cpw1 D) (syn_cvv) (syn_cvv) (syn_c2nd) (syn_chnwcutrel R D)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_sifmap (syn_cpw1 D) (syn_cvv) (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_ffn (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
  have p0014 :=
    Nominal.mp p0012 p0013
  exact p0014

noncomputable def g_wecutcardfactorval
    (D : Class) (R : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_R_q : q ∉ R.fv) (hyp_wecutcardfactorval_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_cwecutcardfactor R D) (.cv q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({q} : Finset Var)
  have p0000 :=
    (by simpa [syn_cwecutcardfactor] using (Nominal.classEqRefl (syn_cwecutcardfactor R D)))
  have p0001 :=
    @g_fveq1i (.cv q) (syn_cwecutcardfactor R D) (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) p0000
  have p0002 :=
    @g_a1i (.classEq (syn_cfv (syn_cwecutcardfactor R D) (.cv q)) (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (.cv q))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0001
  have p0003 :=
    @g_wecutcardsiliftfn D R hyp_wecutcardfactorval_1
  have p0004 :=
    @g_a1i (syn_wfn (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0003
  have p0005 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0006 :=
    @g_jca (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_wfn (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0004 p0005
  have p0007 :=
    @g_fvco2 (syn_cpw1 (syn_cpw1 D)) (.cv q) (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))
  have p0008 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_wa (syn_wfn (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classEq (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (.cv q)) (syn_cfv (syn_cimage (syn_cen)) (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (.cv q)))) p0006 p0007
  have p0009 :=
    @g_pw12argcl (.cv q) D
  have p0010 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0009
  have p0011 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) p0010
  have p0012 :=
    @g_pw12argcl (.cv q) D
  have p0013 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0012
  have p0014 :=
    @g_snelpw1 (syn_cuni (syn_cuni (.cv q))) D
  have p0015 :=
    @g_biimpri (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) (.classMem (syn_cuni (syn_cuni (.cv q))) D) p0014
  have p0016 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) p0013 p0015
  have p0017 :=
    @g_wecutcardinnerf D R hyp_wecutcardfactorval_1
  have p0018 :=
    @g_sifvald (syn_cpw1 D) (syn_cvv) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) p0017
  have p0019 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) (.classEq (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0016 p0018
  have p0020 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0011 p0019
  have p0021 :=
    @g_wecutcardhrelfn D R hyp_wecutcardfactorval_1
  have p0022 :=
    @g_a1i (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0021
  have p0023 :=
    @g_pw12argcl (.cv q) D
  have p0024 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0023
  have p0025 :=
    @g_snelpw1 (syn_cuni (syn_cuni (.cv q))) D
  have p0026 :=
    @g_biimpri (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) (.classMem (syn_cuni (syn_cuni (.cv q))) D) p0025
  have p0027 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) p0024 p0026
  have p0028 :=
    @g_jca (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) p0022 p0027
  have p0029 :=
    @g_fvco2 (syn_cpw1 D) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_c2nd) (syn_chnwcutrel R D)
  have p0030 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_wa (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D))) (.classEq (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0028 p0029
  have p0031 :=
    @g_pw12argcl (.cv q) D
  have p0032 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0031
  have p0033 :=
    @g_hnwcutrelvalcld (syn_cuni (syn_cuni (.cv q))) D R hyp_wecutcardfactorval_1
  have p0034 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) p0032 p0033
  have p0035 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_c2nd) p0034
  have p0036 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) p0030 p0035
  have p0037 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))))
  have p0038 :=
    @g_fveq2i (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_c2nd) p0037
  have p0039 :=
    @g_brex R D (syn_cwe)
  have p0040 :=
    Nominal.mp hyp_wecutcardfactorval_1 p0039
  have p0041 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0040
  have p0042 :=
    @g_brex R D (syn_cwe)
  have p0043 :=
    Nominal.mp hyp_wecutcardfactorval_1 p0042
  have p0044 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0043
  have p0045 :=
    @g_brex R D (syn_cwe)
  have p0046 :=
    Nominal.mp hyp_wecutcardfactorval_1 p0045
  have p0047 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0046
  have p0048 :=
    @g_idex
  have p0049 :=
    @g_difex R (syn_cid) p0047 p0048
  have p0050 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0049
  have p0051 :=
    @g_snex (syn_cuni (syn_cuni (.cv q)))
  have p0052 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))) p0050 p0051
  have p0053 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))) p0044 p0052
  have p0054 :=
    @g_brex R D (syn_cwe)
  have p0055 :=
    Nominal.mp hyp_wecutcardfactorval_1 p0054
  have p0056 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0055
  have p0057 :=
    @g_brex R D (syn_cwe)
  have p0058 :=
    Nominal.mp hyp_wecutcardfactorval_1 p0057
  have p0059 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0058
  have p0060 :=
    @g_idex
  have p0061 :=
    @g_difex R (syn_cid) p0059 p0060
  have p0062 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0061
  have p0063 :=
    @g_snex (syn_cuni (syn_cuni (.cv q)))
  have p0064 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))) p0062 p0063
  have p0065 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))) p0056 p0064
  have p0066 :=
    @g_xpex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0053 p0065
  have p0067 :=
    @g_inex R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0041 p0066
  have p0068 :=
    @g_brex R D (syn_cwe)
  have p0069 :=
    Nominal.mp hyp_wecutcardfactorval_1 p0068
  have p0070 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0069
  have p0071 :=
    @g_brex R D (syn_cwe)
  have p0072 :=
    Nominal.mp hyp_wecutcardfactorval_1 p0071
  have p0073 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0072
  have p0074 :=
    @g_idex
  have p0075 :=
    @g_difex R (syn_cid) p0073 p0074
  have p0076 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0075
  have p0077 :=
    @g_snex (syn_cuni (syn_cuni (.cv q)))
  have p0078 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))) p0076 p0077
  have p0079 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))) p0070 p0078
  have p0080 :=
    @g_opfv2nd (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0067 p0079
  have p0081 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0038 p0080
  have p0082 :=
    @g_a1i (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0081
  have p0083 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0036 p0082
  have p0084 :=
    @g_sneqd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0083
  have p0085 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (.cv q)) (syn_csn (syn_cfv (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0020 p0084
  have p0086 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (.cv q)) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_cimage (syn_cen)) p0085
  have p0087 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (.cv q)) (syn_cfv (syn_cimage (syn_cen)) (syn_cfv (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))) (.cv q))) (syn_cfv (syn_cimage (syn_cen)) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) p0008 p0086
  have p0088 :=
    @g_enex
  have p0089 :=
    @g_snex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0090 :=
    @g_fvimagecl (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_cen) p0088 p0089
  have p0091 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cen))))
  have p0092 :=
    @g_eqcomi (syn_cec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cen)) (syn_cima (syn_cen) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) p0091
  have p0093 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cen)) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cima (syn_cen) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cen)) p0090 p0092
  have p0094 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
  have p0095 :=
    @g_eqcomi (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_cec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cen)) p0094
  have p0096 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cen)) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_cen)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0093 p0095
  have p0097 :=
    @g_a1i (.classEq (syn_cfv (syn_cimage (syn_cen)) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0096
  have p0098 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (.cv q)) (syn_cfv (syn_cimage (syn_cen)) (syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0087 p0097
  have p0099 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_cwecutcardfactor R D) (.cv q)) (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D)))) (.cv q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0002 p0098
  exact p0099

noncomputable def g_wecutcardfnval
    (D : Class) (R : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_R_q : q ∉ R.fv) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_cwecutcardfn R D) (.cv q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({q} : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_q : p ≠ q := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, fresh_p_not_R, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wecutcardfn D R p dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_a1i (.classEq (syn_cwecutcardfn R D) (syn_cmpt p (syn_cpw1 (syn_cpw1 D)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv p))))))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0000
  have p0002 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q))
  have p0003 :=
    @g_unieq (.cv p) (.cv q)
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q))) (.classEq (.cv p) (.cv q)) (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q))) p0002 p0003
  have p0005 :=
    @g_unieqd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q))) (syn_cuni (.cv p)) (syn_cuni (.cv q)) p0004
  have p0006 :=
    @g_sneqd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q))) (syn_cuni (syn_cuni (.cv p))) (syn_cuni (syn_cuni (.cv q))) p0005
  have p0007 :=
    @g_imaeq2d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q))) (syn_csn (syn_cuni (syn_cuni (.cv p)))) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_ccnv (syn_cdif R (syn_cid))) p0006
  have p0008 :=
    @g_ineq2d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv p))))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))) D p0007
  have p0009 :=
    @g_nceqd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv p) (.cv q))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv p)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0008
  have p0010 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0011 :=
    @g_ncex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0012 :=
    @g_a1i (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_cvv)) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0011
  have p0013 :=
    @g_fvmptd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p (.cv q) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv p))))))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_cpw1 (syn_cpw1 D)) (syn_cwecutcardfn R D) (syn_cvv) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0001 p0009 p0010 p0012
  exact p0013

noncomputable def g_wecutcardfnfactor
    (D : Class) (R : Class) (hyp_wecutcardfnfactor_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classEq (syn_cwecutcardfn R D) (syn_cwecutcardfactor R D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cwecutcardfn R D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cwecutcardfactor R D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfactor, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wecutcardfnval D R q dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_wecutcardfactorval D R q dv_cache_0001 dv_cache_0002 hyp_wecutcardfnfactor_1
  have p0002 :=
    @g_eqcomd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_cwecutcardfactor R D) (.cv q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0001
  have p0003 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_cwecutcardfn R D) (.cv q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_cfv (syn_cwecutcardfactor R D) (.cv q)) p0000 p0002
  have p0004 :=
    @g_rgen (.classEq (syn_cfv (syn_cwecutcardfn R D) (.cv q)) (syn_cfv (syn_cwecutcardfactor R D) (.cv q))) q (syn_cpw1 (syn_cpw1 D)) p0003
  have p0005 :=
    @g_wecutcardfnfn D R
  have p0006 :=
    @g_wecutcardfactorfn D R hyp_wecutcardfnfactor_1
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cwecutcardfn R D) (syn_cpw1 (syn_cpw1 D))) (syn_wfn (syn_cwecutcardfactor R D) (syn_cpw1 (syn_cpw1 D))) p0005 p0006
  have p0008 :=
    @g_eqfnfv q (syn_cpw1 (syn_cpw1 D)) (syn_cwecutcardfn R D) (syn_cwecutcardfactor R D) dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_mpbir (.classEq (syn_cwecutcardfn R D) (syn_cwecutcardfactor R D)) (syn_wral q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cfv (syn_cwecutcardfn R D) (.cv q)) (syn_cfv (syn_cwecutcardfactor R D) (.cv q)))) p0004 p0009
  exact p0010

noncomputable def g_wecutcardfnex
    (D : Class) (R : Class) (hyp_wecutcardfnex_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.classMem (syn_cwecutcardfn R D) (syn_cvv)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_wecutcardfnfactor D R hyp_wecutcardfnex_1
  have p0001 :=
    @g_wecutcardfactorex D R hyp_wecutcardfnex_1
  have p0002 :=
    @g_eqeltri (syn_cwecutcardfn R D) (syn_cwecutcardfactor R D) (syn_cvv) p0000 p0001
  exact p0002

noncomputable def g_wecutcardpreimandv
    (D : Class) (R : Class) (K : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_R_q : q ∉ R.fv) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_wb (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ K.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ncex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wecutcardfn D R q dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_fnmpti q (syn_cpw1 (syn_cpw1 D)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) (syn_cwecutcardfn R D) dv_cache_0003 p0000 p0001
  have p0003 :=
    @g_elpreima (syn_cpw1 (syn_cpw1 D)) (.cv q) K (syn_cwecutcardfn R D)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_a1i (syn_wb (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0004
  have p0006 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0007 :=
    @g_biantrurd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K) p0006
  have p0008 :=
    @g_bicomd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K)) p0007
  have p0009 :=
    @g_bitrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K)) (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K) p0005 p0008
  have p0010 :=
    @g_wecutcardfnval D R q dv_cache_0001 dv_cache_0002
  have p0011 :=
    @g_eleq1d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_cfv (syn_cwecutcardfn R D) (.cv q)) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K p0010
  have p0012 :=
    @g_bitrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (.classMem (syn_cfv (syn_cwecutcardfn R D) (.cv q)) K) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K) p0009 p0011
  exact p0012

#print axioms g_wecutcardpreimandv

end NFChoice.DirectNominalPrf.WPPReplay
