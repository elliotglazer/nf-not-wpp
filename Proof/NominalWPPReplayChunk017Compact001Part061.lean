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
import NominalWPPReplayChunk017Compact001Part060

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

noncomputable def g_wppcandprefixpointbidv
    (D : Class) (F : Class) (G : Class) (L : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_F_q : q ∉ F.fv) (dv_G_q : q ∉ G.fv) (dv_L_q : q ∉ L.fv) (hyp_wppcandprefixpointbidv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppcandprefixpointbidv_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wppcandprefixpointbidv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppcandprefixpointbidv_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppcandprefixpointbidv_5 : Nominal.NPrf (.classMem D (syn_cdm G))) (hyp_wppcandprefixpointbidv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wppcandprefixpointbidv_7 : Nominal.NPrf (.classMem L (syn_cvv))) (hyp_wppcandprefixpointbidv_8 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F D) (.cv q)) (syn_clec) L)))) (hyp_wppcandprefixpointbidv_9 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec F D) (.cv q)) (syn_clec) L) (.classEq (syn_cfv G (syn_cfv (syn_cfrec F D) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv q))))))) (hyp_wppcandprefixpointbidv_10 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G D) (.cv q)) (syn_clec) L)))) (hyp_wppcandprefixpointbidv_11 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec G D) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G D) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G D) (.cv q))))))) :
    Nominal.NPrf (syn_wb (.classMem D (syn_cwppcand F L)) (.classMem D (syn_cwppcand G L))) := by
  let proofSupport : Finset Var := D.fv ∪ F.fv ∪ G.fv ∪ L.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elwppcand L D F
  have p0001 :=
    @g_biid (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) L))
  have p0002 :=
    @g_wppreachprefixbidv D F G L q dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_wppcandprefixpointbidv_1 hyp_wppcandprefixpointbidv_2 hyp_wppcandprefixpointbidv_3 hyp_wppcandprefixpointbidv_4 hyp_wppcandprefixpointbidv_5 hyp_wppcandprefixpointbidv_6 hyp_wppcandprefixpointbidv_7 hyp_wppcandprefixpointbidv_8 hyp_wppcandprefixpointbidv_9 hyp_wppcandprefixpointbidv_10 hyp_wppcandprefixpointbidv_11
  have p0003 :=
    @g_anbi12i (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) L)) (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) L)) (.classMem D (syn_cwppreach F L)) (.classMem D (syn_cwppreach G L)) p0001 p0002
  have p0004 :=
    @g_bitri (.classMem D (syn_cwppcand F L)) (syn_wa (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) L)) (.classMem D (syn_cwppreach F L))) (syn_wa (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) L)) (.classMem D (syn_cwppreach G L))) p0000 p0003
  have p0005 :=
    @g_elwppcand L D G
  have p0006 :=
    @g_bicomi (.classMem D (syn_cwppcand G L)) (syn_wa (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) L)) (.classMem D (syn_cwppreach G L))) p0005
  have p0007 :=
    @g_bitri (.classMem D (syn_cwppcand F L)) (syn_wa (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) L)) (.classMem D (syn_cwppreach G L))) (.classMem D (syn_cwppcand G L)) p0004 p0006
  exact p0007

noncomputable def g_wppgammaprefixeqpointndv
    (F : Class) (G : Class) (L : Class) (q : Var) (dv_F_q : q ∉ F.fv) (dv_G_q : q ∉ G.fv) (dv_L_q : q ∉ L.fv) (hyp_wppgammaprefixeqpointndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppgammaprefixeqpointndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppgammaprefixeqpointndv_3 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppgammaprefixeqpointndv_4 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wppgammaprefixeqpointndv_5 : Nominal.NPrf (.classMem L (syn_chwcards (syn_cvv)))) (hyp_wppgammaprefixeqpointndv_6 : Nominal.NPrf (.classMem (syn_cwppgamma F L) (syn_cdm F))) (hyp_wppgammaprefixeqpointndv_7 : Nominal.NPrf (.classMem (syn_cwppgamma F L) (syn_cdm G))) (hyp_wppgammaprefixeqpointndv_8 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)))) (hyp_wppgammaprefixeqpointndv_9 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))))) (hyp_wppgammaprefixeqpointndv_10 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)))) (hyp_wppgammaprefixeqpointndv_11 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))))) (hyp_wppgammaprefixeqpointndv_12 : Nominal.NPrf (.classMem (syn_cwppgamma G L) (syn_cdm F))) (hyp_wppgammaprefixeqpointndv_13 : Nominal.NPrf (.classMem (syn_cwppgamma G L) (syn_cdm G))) (hyp_wppgammaprefixeqpointndv_14 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)))) (hyp_wppgammaprefixeqpointndv_15 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))))) (hyp_wppgammaprefixeqpointndv_16 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)))) (hyp_wppgammaprefixeqpointndv_17 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))))) :
    Nominal.NPrf (.classEq (syn_cwppgamma F L) (syn_cwppgamma G L)) := by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ L.fv ∪ ({q} : Finset Var)
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_k_not_G : k ∉ G.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_not_L : k ∉ L.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_ne_q : k ≠ q := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_k : q ≠ k :=
    Ne.symm fresh_k_ne_q
  have dv_cache_0001 : k ∉ (L).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : k ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cwppgamma G L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_q, dv_G_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : k ∉ ((syn_cwppgamma G L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, fresh_k_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : k ∉ ((syn_cwppcand F L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : k ∉ ((syn_wbr (syn_cwppgamma F L) (syn_clec) (syn_cwppgamma G L))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, fresh_k_not_F, fresh_k_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : q ∉ ((syn_cwppgamma F L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_q, dv_F_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : k ∉ ((syn_cwppgamma F L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : k ∉ ((syn_cwppcand G L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, fresh_k_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : k ∉ ((syn_wbr (syn_cwppgamma G L) (syn_clec) (syn_cwppgamma F L))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, fresh_k_not_G, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex F (syn_cfuns)
  have p0001 :=
    Nominal.mp hyp_wppgammaprefixeqpointndv_1 p0000
  have p0002 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0001 hyp_wppgammaprefixeqpointndv_5
  have p0003 :=
    @g_wppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_simpr (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wral k (syn_cwppcand F L) (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_elex G (syn_cfuns)
  have p0008 :=
    Nominal.mp hyp_wppgammaprefixeqpointndv_3 p0007
  have p0009 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0008 hyp_wppgammaprefixeqpointndv_5
  have p0010 :=
    @g_wppgammaminhwndv L k G dv_cache_0001 dv_cache_0003
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wral k (syn_cwppcand G L) (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)))
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_elex L (syn_chwcards (syn_cvv))
  have p0015 :=
    Nominal.mp hyp_wppgammaprefixeqpointndv_5 p0014
  have p0016 :=
    @g_wppcandprefixpointbidv (syn_cwppgamma G L) F G L q dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_wppgammaprefixeqpointndv_1 hyp_wppgammaprefixeqpointndv_12 hyp_wppgammaprefixeqpointndv_2 hyp_wppgammaprefixeqpointndv_3 hyp_wppgammaprefixeqpointndv_13 hyp_wppgammaprefixeqpointndv_4 p0015 hyp_wppgammaprefixeqpointndv_14 hyp_wppgammaprefixeqpointndv_15 hyp_wppgammaprefixeqpointndv_16 hyp_wppgammaprefixeqpointndv_17
  have p0017 :=
    @g_mpbir (.classMem (syn_cwppgamma G L) (syn_cwppcand F L)) (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) p0013 p0016
  have p0018 :=
    @g_id (.classEq (.cv k) (syn_cwppgamma G L))
  have p0019 :=
    @g_breq2d (.classEq (.cv k) (syn_cwppgamma G L)) (.cv k) (syn_cwppgamma G L) (syn_cwppgamma F L) (syn_clec) p0018
  have p0020 :=
    @g_rspcv (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)) (syn_wbr (syn_cwppgamma F L) (syn_clec) (syn_cwppgamma G L)) k (syn_cwppgamma G L) (syn_cwppcand F L) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0019
  have p0021 :=
    Nominal.mp p0017 p0020
  have p0022 :=
    Nominal.mp p0006 p0021
  have p0023 :=
    @g_elex G (syn_cfuns)
  have p0024 :=
    Nominal.mp hyp_wppgammaprefixeqpointndv_3 p0023
  have p0025 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0024 hyp_wppgammaprefixeqpointndv_5
  have p0026 :=
    @g_wppgammaminhwndv L k G dv_cache_0001 dv_cache_0003
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_simpr (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wral k (syn_cwppcand G L) (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_elex F (syn_cfuns)
  have p0031 :=
    Nominal.mp hyp_wppgammaprefixeqpointndv_1 p0030
  have p0032 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0031 hyp_wppgammaprefixeqpointndv_5
  have p0033 :=
    @g_wppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wral k (syn_cwppcand F L) (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)))
  have p0036 :=
    Nominal.mp p0034 p0035
  have p0037 :=
    @g_elex L (syn_chwcards (syn_cvv))
  have p0038 :=
    Nominal.mp hyp_wppgammaprefixeqpointndv_5 p0037
  have p0039 :=
    @g_wppcandprefixpointbidv (syn_cwppgamma F L) F G L q dv_cache_0011 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_wppgammaprefixeqpointndv_1 hyp_wppgammaprefixeqpointndv_6 hyp_wppgammaprefixeqpointndv_2 hyp_wppgammaprefixeqpointndv_3 hyp_wppgammaprefixeqpointndv_7 hyp_wppgammaprefixeqpointndv_4 p0038 hyp_wppgammaprefixeqpointndv_8 hyp_wppgammaprefixeqpointndv_9 hyp_wppgammaprefixeqpointndv_10 hyp_wppgammaprefixeqpointndv_11
  have p0040 :=
    @g_mpbi (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (.classMem (syn_cwppgamma F L) (syn_cwppcand G L)) p0036 p0039
  have p0041 :=
    @g_id (.classEq (.cv k) (syn_cwppgamma F L))
  have p0042 :=
    @g_breq2d (.classEq (.cv k) (syn_cwppgamma F L)) (.cv k) (syn_cwppgamma F L) (syn_cwppgamma G L) (syn_clec) p0041
  have p0043 :=
    @g_rspcv (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)) (syn_wbr (syn_cwppgamma G L) (syn_clec) (syn_cwppgamma F L)) k (syn_cwppgamma F L) (syn_cwppcand G L) dv_cache_0012 dv_cache_0013 dv_cache_0014 p0042
  have p0044 :=
    Nominal.mp p0040 p0043
  have p0045 :=
    Nominal.mp p0029 p0044
  have p0046 :=
    @g_pm3_2i (syn_wbr (syn_cwppgamma F L) (syn_clec) (syn_cwppgamma G L)) (syn_wbr (syn_cwppgamma G L) (syn_clec) (syn_cwppgamma F L)) p0022 p0045
  have p0047 :=
    @g_elex F (syn_cfuns)
  have p0048 :=
    Nominal.mp hyp_wppgammaprefixeqpointndv_1 p0047
  have p0049 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0048 hyp_wppgammaprefixeqpointndv_5
  have p0050 :=
    @g_wppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0051 :=
    Nominal.mp p0049 p0050
  have p0052 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wral k (syn_cwppcand F L) (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)))
  have p0053 :=
    Nominal.mp p0051 p0052
  have p0054 :=
    @g_elwppcand L (syn_cwppgamma F L) F
  have p0055 :=
    @g_mpbi (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))) p0053 p0054
  have p0056 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))
  have p0057 :=
    Nominal.mp p0055 p0056
  have p0058 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)
  have p0059 :=
    Nominal.mp p0057 p0058
  have p0060 :=
    @g_hwcardssnc (syn_cvv)
  have p0061 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cwppgamma F L) p0060
  have p0062 :=
    Nominal.mp p0059 p0061
  have p0063 :=
    @g_elex G (syn_cfuns)
  have p0064 :=
    Nominal.mp hyp_wppgammaprefixeqpointndv_3 p0063
  have p0065 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0064 hyp_wppgammaprefixeqpointndv_5
  have p0066 :=
    @g_wppgammaminhwndv L k G dv_cache_0001 dv_cache_0003
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wral k (syn_cwppcand G L) (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)))
  have p0069 :=
    Nominal.mp p0067 p0068
  have p0070 :=
    @g_elwppcand L (syn_cwppgamma G L) G
  have p0071 :=
    @g_mpbi (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))) p0069 p0070
  have p0072 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))
  have p0073 :=
    Nominal.mp p0071 p0072
  have p0074 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_hwcardssnc (syn_cvv)
  have p0077 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cwppgamma G L) p0076
  have p0078 :=
    Nominal.mp p0075 p0077
  have p0079 :=
    @g_pm3_2i (.classMem (syn_cwppgamma F L) (syn_cncs)) (.classMem (syn_cwppgamma G L) (syn_cncs)) p0062 p0078
  have p0080 :=
    @g_sbth (syn_cwppgamma F L) (syn_cwppgamma G L)
  have p0081 :=
    Nominal.mp p0079 p0080
  have p0082 :=
    Nominal.mp p0046 p0081
  exact p0082

noncomputable def g_wecomparisonnclecclndv
    (D : Class) (R : Class) (S : Class) (E : Class) (hyp_wecomparisonnclecclndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecomparisonnclecclndv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (syn_wo (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let h : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_h_not_R : h ∉ R.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_h_not_S : h ∉ S.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_E : h ∉ E.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_h_ne_x : h ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_h : x ≠ h :=
    Ne.symm fresh_h_ne_x
  have dv_cache_0001 : h ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : h ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : h ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : h ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have p0000 :=
    @g_wecomparisonterminalfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_wecomparisonnclecclndv_1 hyp_wecomparisonnclecclndv_2
  have p0001 :=
    @g_orc (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
  have p0002 :=
    @g_wecomparisonforwardnclecclfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_wecomparisonnclecclndv_2
  have p0003 :=
    @g_syl (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) p0001 p0002
  have p0004 :=
    @g_orc (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D))
  have p0005 :=
    @g_syl (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wo (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D))) p0003 p0004
  have p0006 :=
    @g_olc (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wex h (syn_wiso (.cv h) R S D E))
  have p0007 :=
    @g_wecomparisonforwardnclecclfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_wecomparisonnclecclndv_2
  have p0008 :=
    @g_syl (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) p0006 p0007
  have p0009 :=
    @g_orc (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D))
  have p0010 :=
    @g_syl (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wo (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D))) p0008 p0009
  have p0011 :=
    @g_olc (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wex h (syn_wiso (.cv h) S R E D))
  have p0012 :=
    @g_wecomparisonforwardnclecclfdv x E S R h D dv_cache_0003 dv_cache_0004 dv_cache_0001 dv_cache_0002 dv_cache_0007 dv_cache_0008 dv_cache_0005 dv_cache_0006 dv_cache_0009 hyp_wecomparisonnclecclndv_1
  have p0013 :=
    @g_syl (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wo (syn_wex h (syn_wiso (.cv h) S R E D)) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D)) p0011 p0012
  have p0014 :=
    @g_olc (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D)) (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))
  have p0015 :=
    @g_syl (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D)) (syn_wo (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D))) p0013 p0014
  have p0016 :=
    @g_n_3jaoi (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wo (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D))) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) p0005 p0010 p0015
  have p0017 :=
    Nominal.mp p0000 p0016
  exact p0017

noncomputable def g_wecomparisonnclecandndv
    (e : Var) (s : Var) (r : Var) (d : Var) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wbr (.cv s) (syn_cwe) (.cv e))) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d))))) := by
  let proofSupport : Finset Var := ({e} : Finset Var) ∪ ({s} : Finset Var) ∪ ({r} : Finset Var) ∪ ({d} : Finset Var)
  have p0000 :=
    @g_biid (.imp (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d)))))
  have p0001 :=
    @g_a1i (syn_wb (.imp (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d))))) (.imp (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d)))))) (.classEq (.cv s) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin)))) p0000
  have p0002 :=
    @g_id (.classEq (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))
  have p0003 :=
    @g_nceqd (.classEq (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)) p0002
  have p0004 :=
    @g_breq2d (.classEq (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_cnc (.cv e)) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_cnc (.cv d)) (syn_clec) p0003
  have p0005 :=
    @g_id (.classEq (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))
  have p0006 :=
    @g_nceqd (.classEq (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)) p0005
  have p0007 :=
    @g_breq1d (.classEq (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_cnc (.cv e)) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_cnc (.cv d)) (syn_clec) p0006
  have p0008 :=
    @g_orbi12d (.classEq (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (.cv d))) p0004 p0007
  have p0009 :=
    @g_imbi2d (.classEq (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d)))) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (.cv d)))) (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0008
  have p0010 :=
    @g_biid (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (.cv d))))
  have p0011 :=
    @g_a1i (syn_wb (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (.cv d)))) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (.cv d))))) (.classEq (.cv r) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin)))) p0010
  have p0012 :=
    @g_id (.classEq (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc)))
  have p0013 :=
    @g_nceqd (.classEq (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc)) p0012
  have p0014 :=
    @g_breq1d (.classEq (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (syn_cnc (.cv d)) (syn_cnc (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) p0013
  have p0015 :=
    @g_id (.classEq (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc)))
  have p0016 :=
    @g_nceqd (.classEq (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc)) p0015
  have p0017 :=
    @g_breq2d (.classEq (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (syn_cnc (.cv d)) (syn_cnc (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) p0016
  have p0018 :=
    @g_orbi12d (.classEq (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (.cv d))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc)))) p0014 p0017
  have p0019 :=
    @g_id (.classEq (.cv r) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin))))
  have p0020 :=
    @g_breq1d (.classEq (.cv r) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin)))) (.cv r) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin))) (.cv d) (syn_cwe) p0019
  have p0021 :=
    @g_id (.classEq (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc)))
  have p0022 :=
    @g_breq2d (.classEq (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (.cv d) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc)) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin))) (syn_cwe) p0021
  have p0023 :=
    @g_id (.classEq (syn_ckqrel (syn_clefin)) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin))))
  have p0024 :=
    @g_breq1d (.classEq (syn_ckqrel (syn_clefin)) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin)))) (syn_ckqrel (syn_clefin)) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin))) (syn_cnnc) (syn_cwe) p0023
  have p0025 :=
    @g_id (.classEq (syn_cnnc) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc)))
  have p0026 :=
    @g_breq2d (.classEq (syn_cnnc) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (syn_cnnc) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc)) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin))) (syn_cwe) p0025
  have p0027 :=
    @g_finlewe
  have p0028 :=
    @g_elimhyp2v (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wbr (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin))) (syn_cwe) (.cv d)) (syn_wbr (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin))) (syn_cwe) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wbr (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin))) (syn_cwe) (syn_cnnc)) (.cv r) (.cv d) (syn_ckqrel (syn_clefin)) (syn_cnnc) p0020 p0022 p0024 p0026 p0027
  have p0029 :=
    @g_id (.classEq (.cv s) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin))))
  have p0030 :=
    @g_breq1d (.classEq (.cv s) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin)))) (.cv s) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin))) (.cv e) (syn_cwe) p0029
  have p0031 :=
    @g_id (.classEq (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))
  have p0032 :=
    @g_breq2d (.classEq (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (.cv e) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin))) (syn_cwe) p0031
  have p0033 :=
    @g_id (.classEq (syn_ckqrel (syn_clefin)) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin))))
  have p0034 :=
    @g_breq1d (.classEq (syn_ckqrel (syn_clefin)) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin)))) (syn_ckqrel (syn_clefin)) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin))) (syn_cnnc) (syn_cwe) p0033
  have p0035 :=
    @g_id (.classEq (syn_cnnc) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))
  have p0036 :=
    @g_breq2d (.classEq (syn_cnnc) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_cnnc) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin))) (syn_cwe) p0035
  have p0037 :=
    @g_finlewe
  have p0038 :=
    @g_elimhyp2v (syn_wbr (.cv s) (syn_cwe) (.cv e)) (syn_wbr (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin))) (syn_cwe) (.cv e)) (syn_wbr (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin))) (syn_cwe) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wbr (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin))) (syn_cwe) (syn_cnnc)) (.cv s) (.cv e) (syn_ckqrel (syn_clefin)) (syn_cnnc) p0030 p0032 p0034 p0036 p0037
  have p0039 :=
    @g_wecomparisonnclecclndv (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc)) (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv r) (syn_ckqrel (syn_clefin))) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv s) (syn_ckqrel (syn_clefin))) (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)) p0028 p0038
  have p0040 :=
    @g_dedth2v (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (.cv d)))) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (.cv d)))) (syn_wo (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (syn_cnnc))))) (.cv r) (.cv d) (syn_ckqrel (syn_clefin)) (syn_cnnc) p0011 p0018 p0039
  have p0041 :=
    @g_dedth2v (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.imp (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d))))) (.imp (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d))))) (.imp (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cif (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.cv e) (syn_cnnc))) (syn_clec) (syn_cnc (.cv d))))) (.cv s) (.cv e) (syn_ckqrel (syn_clefin)) (syn_cnnc) p0001 p0009 p0040
  have p0042 :=
    @g_impcom (syn_wbr (.cv s) (syn_cwe) (.cv e)) (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d)))) p0041
  exact p0042

#print axioms g_wecomparisonnclecandndv

end NFChoice.DirectNominalPrf.WPPReplay
