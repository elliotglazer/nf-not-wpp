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
import NominalWPPReplayChunk017Compact001Part062

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

noncomputable def g_wppgammaprefixeqhwselfmapndv
    (y : Var) (F : Class) (G : Class) (L : Class) (dv_F_y : y ∉ F.fv) (dv_G_y : y ∉ G.fv) (dv_L_y : y ∉ L.fv) (hyp_wppgammaprefixeqhwselfmapndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppgammaprefixeqhwselfmapndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppgammaprefixeqhwselfmapndv_3 : Nominal.NPrf (.classEq (syn_cdm F) (syn_chwcards (syn_cvv)))) (hyp_wppgammaprefixeqhwselfmapndv_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppgammaprefixeqhwselfmapndv_5 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wppgammaprefixeqhwselfmapndv_6 : Nominal.NPrf (.classEq (syn_cdm G) (syn_chwcards (syn_cvv)))) (hyp_wppgammaprefixeqhwselfmapndv_7 : Nominal.NPrf (.classMem L (syn_chwcards (syn_cvv)))) (hyp_wppgammaprefixeqhwselfmapndv_8 : Nominal.NPrf (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))))) :
    Nominal.NPrf (.classEq (syn_cwppgamma F L) (syn_cwppgamma G L)) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ F.fv ∪ G.fv ∪ L.fv
  let q : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_y : q ≠ y := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_q : y ≠ q :=
    Ne.symm fresh_q_ne_y
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_G : q ∉ G.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_L : q ∉ L.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_ne_y : k ≠ y := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_k : y ≠ k :=
    Ne.symm fresh_k_ne_y
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_not_G : k ∉ G.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_not_L : k ∉ L.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_q_ne_k : q ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_k_ne_q : k ≠ q :=
    Ne.symm fresh_q_ne_k
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
  have dv_cache_0003 : q ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cwppgamma F L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_L, fresh_q_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_chwcards (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, dv_G_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : k ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((syn_cwppgamma G L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_L, fresh_q_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, dv_G_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, dv_G_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : q ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex F (syn_cfuns)
  have p0001 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_1 p0000
  have p0002 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0001 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0003 :=
    @g_wppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wral k (syn_cwppcand F L) (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_elwppcand L (syn_cwppgamma F L) F
  have p0008 :=
    @g_mpbi (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))) p0006 p0007
  have p0009 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_eleq2i (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppgamma F L) hyp_wppgammaprefixeqhwselfmapndv_3
  have p0014 :=
    @g_mpbir (.classMem (syn_cwppgamma F L) (syn_cdm F)) (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) p0012 p0013
  have p0015 :=
    @g_elex F (syn_cfuns)
  have p0016 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_1 p0015
  have p0017 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0016 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0018 :=
    @g_wppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wral k (syn_cwppcand F L) (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)))
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_elwppcand L (syn_cwppgamma F L) F
  have p0023 :=
    @g_mpbi (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))) p0021 p0022
  have p0024 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_eleq2i (syn_cdm G) (syn_chwcards (syn_cvv)) (syn_cwppgamma F L) hyp_wppgammaprefixeqhwselfmapndv_6
  have p0029 :=
    @g_mpbir (.classMem (syn_cwppgamma F L) (syn_cdm G)) (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) p0027 p0028
  have p0030 :=
    @g_elex F (syn_cfuns)
  have p0031 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_1 p0030
  have p0032 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0031 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0033 :=
    @g_wppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wral k (syn_cwppcand F L) (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)))
  have p0036 :=
    Nominal.mp p0034 p0035
  have p0037 :=
    @g_elwppcand L (syn_cwppgamma F L) F
  have p0038 :=
    @g_mpbi (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))) p0036 p0037
  have p0039 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)
  have p0042 :=
    Nominal.mp p0040 p0041
  have p0043 :=
    @g_eleq2i (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppgamma F L) hyp_wppgammaprefixeqhwselfmapndv_3
  have p0044 :=
    @g_mpbir (.classMem (syn_cwppgamma F L) (syn_cdm F)) (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) p0042 p0043
  have p0045 :=
    @g_wpporbithwcldmndv F (syn_cwppgamma F L) q dv_cache_0003 dv_cache_0004 hyp_wppgammaprefixeqhwselfmapndv_1 p0044 hyp_wppgammaprefixeqhwselfmapndv_2 hyp_wppgammaprefixeqhwselfmapndv_3
  have p0046 :=
    @g_a1i (.classMem L (syn_chwcards (syn_cvv))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) hyp_wppgammaprefixeqhwselfmapndv_7
  have p0047 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0048 :=
    @g_jca (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (.classMem L (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) p0046 p0047
  have p0049 :=
    @g_hwcardslecconnexndv L (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))
  have p0050 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wa (.classMem L (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) p0048 p0049
  have p0051 :=
    @g_notnot (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
  have p0052 :=
    @g_biimpi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))) p0051
  have p0053 :=
    @g_pm2_21 (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
  have p0054 :=
    @g_syl (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) p0052 p0053
  have p0055 :=
    @g_id (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
  have p0056 :=
    @g_a1d (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))) p0055
  have p0057 :=
    @g_jaoi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) p0054 p0056
  have p0058 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) p0050 p0057
  have p0059 :=
    @g_ralimiaa (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) q (syn_cnnc) p0058
  have p0060 :=
    Nominal.mp p0045 p0059
  have p0061 :=
    @g_elex F (syn_cfuns)
  have p0062 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_1 p0061
  have p0063 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0062 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0064 :=
    @g_wppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wral k (syn_cwppcand F L) (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)))
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_elwppcand L (syn_cwppgamma F L) F
  have p0069 :=
    @g_mpbi (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))) p0067 p0068
  have p0070 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))
  have p0071 :=
    Nominal.mp p0069 p0070
  have p0072 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)
  have p0073 :=
    Nominal.mp p0071 p0072
  have p0074 :=
    @g_eleq2i (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppgamma F L) hyp_wppgammaprefixeqhwselfmapndv_3
  have p0075 :=
    @g_mpbir (.classMem (syn_cwppgamma F L) (syn_cdm F)) (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) p0073 p0074
  have p0076 :=
    @g_wpporbithwcldmndv F (syn_cwppgamma F L) q dv_cache_0003 dv_cache_0004 hyp_wppgammaprefixeqhwselfmapndv_1 p0075 hyp_wppgammaprefixeqhwselfmapndv_2 hyp_wppgammaprefixeqhwselfmapndv_3
  have p0077 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0078 :=
    @g_a1i (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) hyp_wppgammaprefixeqhwselfmapndv_8
  have p0079 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
  have p0080 :=
    @g_breq1d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) L (syn_clec) p0079
  have p0081 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
  have p0082 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) F p0081
  have p0083 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
  have p0084 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) G p0083
  have p0085 :=
    @g_eqeq12d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv F (.cv y)) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (.cv y)) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) p0082 p0084
  have p0086 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_wbr (.cv y) (syn_clec) L) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))) p0080 p0085
  have p0087 :=
    @g_rspcv (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))) (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))) y (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0086
  have p0088 :=
    @g_mpd (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))) (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))) p0078 p0087
  have p0089 :=
    @g_impcom (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))) p0088
  have p0090 :=
    @g_eqcomd (syn_wa (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) p0089
  have p0091 :=
    @g_expcom (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))) p0090
  have p0092 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))) p0077 p0091
  have p0093 :=
    @g_ralimiaa (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))) q (syn_cnnc) p0092
  have p0094 :=
    Nominal.mp p0076 p0093
  have p0095 :=
    @g_elex F (syn_cfuns)
  have p0096 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_1 p0095
  have p0097 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0096 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0098 :=
    @g_wppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0099 :=
    Nominal.mp p0097 p0098
  have p0100 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wral k (syn_cwppcand F L) (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)))
  have p0101 :=
    Nominal.mp p0099 p0100
  have p0102 :=
    @g_elwppcand L (syn_cwppgamma F L) F
  have p0103 :=
    @g_mpbi (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))) p0101 p0102
  have p0104 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))
  have p0105 :=
    Nominal.mp p0103 p0104
  have p0106 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)
  have p0107 :=
    Nominal.mp p0105 p0106
  have p0108 :=
    @g_eleq2i (syn_cdm G) (syn_chwcards (syn_cvv)) (syn_cwppgamma F L) hyp_wppgammaprefixeqhwselfmapndv_6
  have p0109 :=
    @g_mpbir (.classMem (syn_cwppgamma F L) (syn_cdm G)) (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) p0107 p0108
  have p0110 :=
    @g_wpporbithwcldmndv G (syn_cwppgamma F L) q dv_cache_0008 dv_cache_0004 hyp_wppgammaprefixeqhwselfmapndv_4 p0109 hyp_wppgammaprefixeqhwselfmapndv_5 hyp_wppgammaprefixeqhwselfmapndv_6
  have p0111 :=
    @g_a1i (.classMem L (syn_chwcards (syn_cvv))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) hyp_wppgammaprefixeqhwselfmapndv_7
  have p0112 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0113 :=
    @g_jca (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (.classMem L (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) p0111 p0112
  have p0114 :=
    @g_hwcardslecconnexndv L (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))
  have p0115 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wa (.classMem L (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) p0113 p0114
  have p0116 :=
    @g_notnot (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
  have p0117 :=
    @g_biimpi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))) p0116
  have p0118 :=
    @g_pm2_21 (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
  have p0119 :=
    @g_syl (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) p0117 p0118
  have p0120 :=
    @g_id (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
  have p0121 :=
    @g_a1d (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))) p0120
  have p0122 :=
    @g_jaoi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) p0119 p0121
  have p0123 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) p0115 p0122
  have p0124 :=
    @g_ralimiaa (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)) q (syn_cnnc) p0123
  have p0125 :=
    Nominal.mp p0110 p0124
  have p0126 :=
    @g_elex F (syn_cfuns)
  have p0127 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_1 p0126
  have p0128 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0127 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0129 :=
    @g_wppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0130 :=
    Nominal.mp p0128 p0129
  have p0131 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wral k (syn_cwppcand F L) (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)))
  have p0132 :=
    Nominal.mp p0130 p0131
  have p0133 :=
    @g_elwppcand L (syn_cwppgamma F L) F
  have p0134 :=
    @g_mpbi (.classMem (syn_cwppgamma F L) (syn_cwppcand F L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))) p0132 p0133
  have p0135 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)) (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))
  have p0136 :=
    Nominal.mp p0134 p0135
  have p0137 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma F L) (syn_clec) L)
  have p0138 :=
    Nominal.mp p0136 p0137
  have p0139 :=
    @g_eleq2i (syn_cdm G) (syn_chwcards (syn_cvv)) (syn_cwppgamma F L) hyp_wppgammaprefixeqhwselfmapndv_6
  have p0140 :=
    @g_mpbir (.classMem (syn_cwppgamma F L) (syn_cdm G)) (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) p0138 p0139
  have p0141 :=
    @g_wpporbithwcldmndv G (syn_cwppgamma F L) q dv_cache_0008 dv_cache_0004 hyp_wppgammaprefixeqhwselfmapndv_4 p0140 hyp_wppgammaprefixeqhwselfmapndv_5 hyp_wppgammaprefixeqhwselfmapndv_6
  have p0142 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0143 :=
    @g_a1i (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) hyp_wppgammaprefixeqhwselfmapndv_8
  have p0144 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
  have p0145 :=
    @g_breq1d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) L (syn_clec) p0144
  have p0146 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
  have p0147 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) F p0146
  have p0148 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
  have p0149 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) G p0148
  have p0150 :=
    @g_eqeq12d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_cfv F (.cv y)) (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (.cv y)) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) p0147 p0149
  have p0151 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_wbr (.cv y) (syn_clec) L) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))) p0145 p0150
  have p0152 :=
    @g_rspcv (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))) (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))) y (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)) dv_cache_0009 dv_cache_0006 dv_cache_0010 p0151
  have p0153 :=
    @g_mpd (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))) (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))) p0143 p0152
  have p0154 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))) p0142 p0153
  have p0155 :=
    @g_ralimiaa (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))) q (syn_cnnc) p0154
  have p0156 :=
    Nominal.mp p0141 p0155
  have p0157 :=
    @g_elex G (syn_cfuns)
  have p0158 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_4 p0157
  have p0159 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0158 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0160 :=
    @g_wppgammaminhwndv L k G dv_cache_0001 dv_cache_0011
  have p0161 :=
    Nominal.mp p0159 p0160
  have p0162 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wral k (syn_cwppcand G L) (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)))
  have p0163 :=
    Nominal.mp p0161 p0162
  have p0164 :=
    @g_elwppcand L (syn_cwppgamma G L) G
  have p0165 :=
    @g_mpbi (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))) p0163 p0164
  have p0166 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))
  have p0167 :=
    Nominal.mp p0165 p0166
  have p0168 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)
  have p0169 :=
    Nominal.mp p0167 p0168
  have p0170 :=
    @g_eleq2i (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppgamma G L) hyp_wppgammaprefixeqhwselfmapndv_3
  have p0171 :=
    @g_mpbir (.classMem (syn_cwppgamma G L) (syn_cdm F)) (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) p0169 p0170
  have p0172 :=
    @g_elex G (syn_cfuns)
  have p0173 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_4 p0172
  have p0174 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0173 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0175 :=
    @g_wppgammaminhwndv L k G dv_cache_0001 dv_cache_0011
  have p0176 :=
    Nominal.mp p0174 p0175
  have p0177 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wral k (syn_cwppcand G L) (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)))
  have p0178 :=
    Nominal.mp p0176 p0177
  have p0179 :=
    @g_elwppcand L (syn_cwppgamma G L) G
  have p0180 :=
    @g_mpbi (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))) p0178 p0179
  have p0181 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))
  have p0182 :=
    Nominal.mp p0180 p0181
  have p0183 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)
  have p0184 :=
    Nominal.mp p0182 p0183
  have p0185 :=
    @g_eleq2i (syn_cdm G) (syn_chwcards (syn_cvv)) (syn_cwppgamma G L) hyp_wppgammaprefixeqhwselfmapndv_6
  have p0186 :=
    @g_mpbir (.classMem (syn_cwppgamma G L) (syn_cdm G)) (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) p0184 p0185
  have p0187 :=
    @g_elex G (syn_cfuns)
  have p0188 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_4 p0187
  have p0189 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0188 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0190 :=
    @g_wppgammaminhwndv L k G dv_cache_0001 dv_cache_0011
  have p0191 :=
    Nominal.mp p0189 p0190
  have p0192 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wral k (syn_cwppcand G L) (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)))
  have p0193 :=
    Nominal.mp p0191 p0192
  have p0194 :=
    @g_elwppcand L (syn_cwppgamma G L) G
  have p0195 :=
    @g_mpbi (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))) p0193 p0194
  have p0196 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))
  have p0197 :=
    Nominal.mp p0195 p0196
  have p0198 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)
  have p0199 :=
    Nominal.mp p0197 p0198
  have p0200 :=
    @g_eleq2i (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppgamma G L) hyp_wppgammaprefixeqhwselfmapndv_3
  have p0201 :=
    @g_mpbir (.classMem (syn_cwppgamma G L) (syn_cdm F)) (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) p0199 p0200
  have p0202 :=
    @g_wpporbithwcldmndv F (syn_cwppgamma G L) q dv_cache_0003 dv_cache_0012 hyp_wppgammaprefixeqhwselfmapndv_1 p0201 hyp_wppgammaprefixeqhwselfmapndv_2 hyp_wppgammaprefixeqhwselfmapndv_3
  have p0203 :=
    @g_a1i (.classMem L (syn_chwcards (syn_cvv))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) hyp_wppgammaprefixeqhwselfmapndv_7
  have p0204 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0205 :=
    @g_jca (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (.classMem L (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) p0203 p0204
  have p0206 :=
    @g_hwcardslecconnexndv L (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))
  have p0207 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wa (.classMem L (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) p0205 p0206
  have p0208 :=
    @g_notnot (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
  have p0209 :=
    @g_biimpi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))) p0208
  have p0210 :=
    @g_pm2_21 (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
  have p0211 :=
    @g_syl (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) p0209 p0210
  have p0212 :=
    @g_id (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
  have p0213 :=
    @g_a1d (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))) p0212
  have p0214 :=
    @g_jaoi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) p0211 p0213
  have p0215 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) p0207 p0214
  have p0216 :=
    @g_ralimiaa (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) q (syn_cnnc) p0215
  have p0217 :=
    Nominal.mp p0202 p0216
  have p0218 :=
    @g_elex G (syn_cfuns)
  have p0219 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_4 p0218
  have p0220 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0219 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0221 :=
    @g_wppgammaminhwndv L k G dv_cache_0001 dv_cache_0011
  have p0222 :=
    Nominal.mp p0220 p0221
  have p0223 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wral k (syn_cwppcand G L) (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)))
  have p0224 :=
    Nominal.mp p0222 p0223
  have p0225 :=
    @g_elwppcand L (syn_cwppgamma G L) G
  have p0226 :=
    @g_mpbi (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))) p0224 p0225
  have p0227 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))
  have p0228 :=
    Nominal.mp p0226 p0227
  have p0229 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)
  have p0230 :=
    Nominal.mp p0228 p0229
  have p0231 :=
    @g_eleq2i (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppgamma G L) hyp_wppgammaprefixeqhwselfmapndv_3
  have p0232 :=
    @g_mpbir (.classMem (syn_cwppgamma G L) (syn_cdm F)) (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) p0230 p0231
  have p0233 :=
    @g_wpporbithwcldmndv F (syn_cwppgamma G L) q dv_cache_0003 dv_cache_0012 hyp_wppgammaprefixeqhwselfmapndv_1 p0232 hyp_wppgammaprefixeqhwselfmapndv_2 hyp_wppgammaprefixeqhwselfmapndv_3
  have p0234 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0235 :=
    @g_a1i (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) hyp_wppgammaprefixeqhwselfmapndv_8
  have p0236 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
  have p0237 :=
    @g_breq1d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) L (syn_clec) p0236
  have p0238 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
  have p0239 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) F p0238
  have p0240 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
  have p0241 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) G p0240
  have p0242 :=
    @g_eqeq12d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv F (.cv y)) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (.cv y)) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) p0239 p0241
  have p0243 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_wbr (.cv y) (syn_clec) L) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))) p0237 p0242
  have p0244 :=
    @g_rspcv (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))) (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))) y (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)) dv_cache_0013 dv_cache_0006 dv_cache_0014 p0243
  have p0245 :=
    @g_mpd (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))) (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))) p0235 p0244
  have p0246 :=
    @g_impcom (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))) p0245
  have p0247 :=
    @g_eqcomd (syn_wa (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) p0246
  have p0248 :=
    @g_expcom (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))) p0247
  have p0249 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))) p0234 p0248
  have p0250 :=
    @g_ralimiaa (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))) q (syn_cnnc) p0249
  have p0251 :=
    Nominal.mp p0233 p0250
  have p0252 :=
    @g_elex G (syn_cfuns)
  have p0253 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_4 p0252
  have p0254 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0253 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0255 :=
    @g_wppgammaminhwndv L k G dv_cache_0001 dv_cache_0011
  have p0256 :=
    Nominal.mp p0254 p0255
  have p0257 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wral k (syn_cwppcand G L) (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)))
  have p0258 :=
    Nominal.mp p0256 p0257
  have p0259 :=
    @g_elwppcand L (syn_cwppgamma G L) G
  have p0260 :=
    @g_mpbi (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))) p0258 p0259
  have p0261 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))
  have p0262 :=
    Nominal.mp p0260 p0261
  have p0263 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)
  have p0264 :=
    Nominal.mp p0262 p0263
  have p0265 :=
    @g_eleq2i (syn_cdm G) (syn_chwcards (syn_cvv)) (syn_cwppgamma G L) hyp_wppgammaprefixeqhwselfmapndv_6
  have p0266 :=
    @g_mpbir (.classMem (syn_cwppgamma G L) (syn_cdm G)) (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) p0264 p0265
  have p0267 :=
    @g_wpporbithwcldmndv G (syn_cwppgamma G L) q dv_cache_0008 dv_cache_0012 hyp_wppgammaprefixeqhwselfmapndv_4 p0266 hyp_wppgammaprefixeqhwselfmapndv_5 hyp_wppgammaprefixeqhwselfmapndv_6
  have p0268 :=
    @g_a1i (.classMem L (syn_chwcards (syn_cvv))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) hyp_wppgammaprefixeqhwselfmapndv_7
  have p0269 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0270 :=
    @g_jca (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (.classMem L (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) p0268 p0269
  have p0271 :=
    @g_hwcardslecconnexndv L (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))
  have p0272 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wa (.classMem L (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) p0270 p0271
  have p0273 :=
    @g_notnot (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
  have p0274 :=
    @g_biimpi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))) p0273
  have p0275 :=
    @g_pm2_21 (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
  have p0276 :=
    @g_syl (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) p0274 p0275
  have p0277 :=
    @g_id (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
  have p0278 :=
    @g_a1d (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))) p0277
  have p0279 :=
    @g_jaoi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) p0276 p0278
  have p0280 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) p0272 p0279
  have p0281 :=
    @g_ralimiaa (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)) q (syn_cnnc) p0280
  have p0282 :=
    Nominal.mp p0267 p0281
  have p0283 :=
    @g_elex G (syn_cfuns)
  have p0284 :=
    Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_4 p0283
  have p0285 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0284 hyp_wppgammaprefixeqhwselfmapndv_7
  have p0286 :=
    @g_wppgammaminhwndv L k G dv_cache_0001 dv_cache_0011
  have p0287 :=
    Nominal.mp p0285 p0286
  have p0288 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wral k (syn_cwppcand G L) (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)))
  have p0289 :=
    Nominal.mp p0287 p0288
  have p0290 :=
    @g_elwppcand L (syn_cwppgamma G L) G
  have p0291 :=
    @g_mpbi (.classMem (syn_cwppgamma G L) (syn_cwppcand G L)) (syn_wa (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))) p0289 p0290
  have p0292 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)) (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))
  have p0293 :=
    Nominal.mp p0291 p0292
  have p0294 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma G L) (syn_clec) L)
  have p0295 :=
    Nominal.mp p0293 p0294
  have p0296 :=
    @g_eleq2i (syn_cdm G) (syn_chwcards (syn_cvv)) (syn_cwppgamma G L) hyp_wppgammaprefixeqhwselfmapndv_6
  have p0297 :=
    @g_mpbir (.classMem (syn_cwppgamma G L) (syn_cdm G)) (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) p0295 p0296
  have p0298 :=
    @g_wpporbithwcldmndv G (syn_cwppgamma G L) q dv_cache_0008 dv_cache_0012 hyp_wppgammaprefixeqhwselfmapndv_4 p0297 hyp_wppgammaprefixeqhwselfmapndv_5 hyp_wppgammaprefixeqhwselfmapndv_6
  have p0299 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0300 :=
    @g_a1i (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) hyp_wppgammaprefixeqhwselfmapndv_8
  have p0301 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
  have p0302 :=
    @g_breq1d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) L (syn_clec) p0301
  have p0303 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
  have p0304 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) F p0303
  have p0305 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
  have p0306 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) G p0305
  have p0307 :=
    @g_eqeq12d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_cfv F (.cv y)) (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (.cv y)) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) p0304 p0306
  have p0308 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_wbr (.cv y) (syn_clec) L) (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))) p0302 p0307
  have p0309 :=
    @g_rspcv (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))) (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))) y (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)) dv_cache_0015 dv_cache_0006 dv_cache_0016 p0308
  have p0310 :=
    @g_mpd (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))) (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))) p0300 p0309
  have p0311 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))) (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))) p0299 p0310
  have p0312 :=
    @g_ralimiaa (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))) q (syn_cnnc) p0311
  have p0313 :=
    Nominal.mp p0298 p0312
  have p0314 :=
    @g_wppgammaprefixeqpointndv F G L q dv_cache_0003 dv_cache_0008 dv_cache_0017 hyp_wppgammaprefixeqhwselfmapndv_1 hyp_wppgammaprefixeqhwselfmapndv_2 hyp_wppgammaprefixeqhwselfmapndv_4 hyp_wppgammaprefixeqhwselfmapndv_5 hyp_wppgammaprefixeqhwselfmapndv_7 p0014 p0029 p0060 p0094 p0125 p0156 p0171 p0186 p0217 p0251 p0282 p0313
  exact p0314

#print axioms g_wppgammaprefixeqhwselfmapndv

end NFChoice.DirectNominalPrf.WPPReplay
