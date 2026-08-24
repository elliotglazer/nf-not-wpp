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
import NominalWPPReplayChunk017Compact001Part059

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

noncomputable def g_wppreachprefixbidv
    (D : Class) (F : Class) (G : Class) (L : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_F_q : q ∉ F.fv) (dv_G_q : q ∉ G.fv) (dv_L_q : q ∉ L.fv) (hyp_wppreachprefixbidv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppreachprefixbidv_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wppreachprefixbidv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppreachprefixbidv_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppreachprefixbidv_5 : Nominal.NPrf (.classMem D (syn_cdm G))) (hyp_wppreachprefixbidv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wppreachprefixbidv_7 : Nominal.NPrf (.classMem L (syn_cvv))) (hyp_wppreachprefixbidv_8 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec F D) (.cv q)) (syn_clec) L)))) (hyp_wppreachprefixbidv_9 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec F D) (.cv q)) (syn_clec) L) (.classEq (syn_cfv G (syn_cfv (syn_cfrec F D) (.cv q))) (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv q))))))) (hyp_wppreachprefixbidv_10 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec G D) (.cv q)) (syn_clec) L)))) (hyp_wppreachprefixbidv_11 : Nominal.NPrf (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec G D) (.cv q)) (syn_clec) L) (.classEq (syn_cfv F (syn_cfv (syn_cfrec G D) (.cv q))) (syn_cfv G (syn_cfv (syn_cfrec G D) (.cv q))))))) :
    Nominal.NPrf (syn_wb (.classMem D (syn_cwppreach F L)) (.classMem D (syn_cwppreach G L))) := by
  let proofSupport : Finset Var := D.fv ∪ F.fv ∪ G.fv ∪ L.fv ∪ ({q} : Finset Var)
  let n : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_L : n ∉ L.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_q : n ≠ q := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_n : q ≠ n :=
    Ne.symm fresh_n_ne_q
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_not_D : k ∉ D.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
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
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_G : r ∉ G.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_L : r ∉ L.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_q : r ≠ q := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_r : q ≠ r :=
    Ne.symm fresh_r_ne_q
  have fresh_n_ne_k : n ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_k_ne_n : k ≠ n :=
    Ne.symm fresh_n_ne_k
  have fresh_n_ne_r : n ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_n : r ≠ n :=
    Ne.symm fresh_n_ne_r
  have fresh_k_ne_r : k ≠ r := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_k : r ≠ k :=
    Ne.symm fresh_k_ne_r
  have dv_cache_0001 : n ∉ (L).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((Wff.classMem (.cv n) (syn_cwpphit F D L))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_n, fresh_r_not_L, fresh_r_not_F, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Wff.classMem (.cv r) (syn_cwpphit F D L))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_r, fresh_n_not_L, fresh_n_not_F, fresh_n_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit F D L)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_r, fresh_n_not_L, fresh_n_not_F, fresh_n_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : k ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : r ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : k ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : r ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : k ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : q ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : r ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : k ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : q ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : r ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : k ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show k ≠ q from (by exact fresh_k_ne_q))
  have dv_cache_0022 : k ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show k ≠ r from (by exact fresh_k_ne_r))
  have dv_cache_0023 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0024 : q ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : k ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : n ∉ ((syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_L, fresh_n_ne_k, fresh_n_not_G, fresh_n_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : k ∉ ((syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, fresh_k_ne_n, fresh_k_not_G, fresh_k_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : k ∉ ((syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, fresh_k_ne_n, fresh_k_not_G, fresh_k_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : n ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : r ∉ ((Wff.classMem (.cv n) (syn_cwpphit G D L))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_n, fresh_r_not_L, fresh_r_not_G, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : n ∉ ((Wff.classMem (.cv r) (syn_cwpphit G D L))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_r, fresh_n_not_L, fresh_n_not_G, fresh_n_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : n ∉ ((syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit G D L)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_r, fresh_n_not_L, fresh_n_not_G, fresh_n_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : k ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : r ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : n ∉ ((syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_L, fresh_n_ne_k, fresh_n_not_F, fresh_n_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : k ∉ ((syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, fresh_k_ne_n, fresh_k_not_F, fresh_k_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : k ∉ ((syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_L, fresh_k_ne_n, fresh_k_not_F, fresh_k_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppreachfwdrexvndv L D n F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wppreachprefixbidv_1 hyp_wppreachprefixbidv_2 hyp_wppreachprefixbidv_3 hyp_wppreachprefixbidv_7
  have p0001 :=
    @g_biimpi (.classMem D (syn_cwppreach F L)) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) p0000
  have p0002 :=
    @g_finlewe
  have p0003 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) p0002
  have p0004 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))
  have p0005 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wppreachprefixbidv_1 hyp_wppreachprefixbidv_2 hyp_wppreachprefixbidv_3
  have p0006 :=
    @g_elwpphitvndv L F D (.cv n)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_biimpri (.classMem (.cv n) (syn_cwpphit F D L)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) p0007
  have p0009 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit F D L)) p0004 p0008
  have p0010 :=
    @g_rspe (.classMem (.cv n) (syn_cwpphit F D L)) n (syn_cnnc)
  have p0011 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit F D L))) (syn_wrex n (syn_cnnc) (.classMem (.cv n) (syn_cwpphit F D L))) p0009 p0010
  have p0012 :=
    @g_id (.classEq (.cv n) (.cv r))
  have p0013 :=
    @g_eleq1d (.classEq (.cv n) (.cv r)) (.cv n) (.cv r) (syn_cwpphit F D L) p0012
  have p0014_e00_recanon : Nominal.NPrf (.imp (.objEq n r) (syn_wb (.classMem (.cv n) (syn_cwpphit F D L)) (.classMem (.cv r) (syn_cwpphit F D L)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0013
  have p0014 :=
    @g_cbvrexv (.classMem (.cv n) (syn_cwpphit F D L)) (.classMem (.cv r) (syn_cwpphit F D L)) n r (syn_cnnc) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0014_e00_recanon
  have p0015 :=
    @g_biimpi (syn_wrex n (syn_cnnc) (.classMem (.cv n) (syn_cwpphit F D L))) (syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit F D L))) p0014
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (syn_wrex n (syn_cnnc) (.classMem (.cv n) (syn_cwpphit F D L))) (syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit F D L))) p0011 p0015
  have p0017 :=
    @g_rexlimiva (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) (syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit F D L))) n (syn_cnnc) dv_cache_0008 p0016
  have p0018 :=
    @g_jca (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit F D L))) p0003 p0017
  have p0019 :=
    @g_elex F (syn_cfuns)
  have p0020 :=
    Nominal.mp hyp_wppreachprefixbidv_1 p0019
  have p0021 :=
    @g_wpphitminexvndv r L (syn_ckqrel (syn_clefin)) k q F D dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 p0020
  have p0022 :=
    @g_syl (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (syn_wa (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit F D L)))) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit F D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) p0018 p0021
  have p0023 :=
    @g_wpphitprefixtransferpackdndv k G F D L q dv_cache_0024 dv_cache_0013 dv_cache_0016 dv_cache_0010 dv_cache_0021 hyp_wppreachprefixbidv_4 hyp_wppreachprefixbidv_5 hyp_wppreachprefixbidv_6 hyp_wppreachprefixbidv_1 hyp_wppreachprefixbidv_2 hyp_wppreachprefixbidv_3 hyp_wppreachprefixbidv_8 hyp_wppreachprefixbidv_9
  have p0024 :=
    @g_simpl (.classMem (.cv k) (syn_cwpphit G D L)) (.classEq (syn_cfv (syn_cfrec F D) (.cv k)) (syn_cfv (syn_cfrec G D) (.cv k)))
  have p0025 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit F D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv k) (syn_cwpphit G D L)) (.classEq (syn_cfv (syn_cfrec F D) (.cv k)) (syn_cfv (syn_cfrec G D) (.cv k)))) (.classMem (.cv k) (syn_cwpphit G D L)) p0023 p0024
  have p0026 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem D (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_wppreachprefixbidv_4 hyp_wppreachprefixbidv_5 hyp_wppreachprefixbidv_6
  have p0027 :=
    @g_elwpphitvndv L G D (.cv k)
  have p0028 :=
    Nominal.mp p0026 p0027
  have p0029 :=
    @g_a1i (syn_wb (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k))))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit F D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) p0028
  have p0030 :=
    @g_biimpd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit F D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k)))) p0029
  have p0031 :=
    @g_mpd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit F D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k)))) p0025 p0030
  have p0032 :=
    @g_rspe (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k))) k (syn_cnnc)
  have p0033 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit F D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k)))) (syn_wrex k (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k)))) p0031 p0032
  have p0034 :=
    @g_id (.classEq (.cv k) (.cv n))
  have p0035 :=
    @g_fveq2d (.classEq (.cv k) (.cv n)) (.cv k) (.cv n) (syn_cfrec G D) p0034
  have p0036 :=
    @g_breq2d (.classEq (.cv k) (.cv n)) (syn_cfv (syn_cfrec G D) (.cv k)) (syn_cfv (syn_cfrec G D) (.cv n)) L (syn_clec) p0035
  have p0037_e00_recanon : Nominal.NPrf (.imp (.objEq k n) (syn_wb (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_clec syn_copab syn_cfv syn_cio syn_cuni syn_csn syn_cfrec syn_cclos1 syn_cint syn_cpprod syn_ctxp syn_cin syn_ccom syn_ccnv syn_c1st syn_cmpt syn_cvv syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0036
  have p0037 :=
    @g_cbvrexv (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n))) k n (syn_cnnc) dv_cache_0025 dv_cache_0004 dv_cache_0026 dv_cache_0027 p0037_e00_recanon
  have p0038 :=
    @g_biimpi (syn_wrex k (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k)))) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) p0037
  have p0039 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit F D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wrex k (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv k)))) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) p0033 p0038
  have p0040 :=
    @g_rexlimiva (syn_wa (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit F D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) k (syn_cnnc) dv_cache_0028 p0039
  have p0041 :=
    @g_syl (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit F D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) p0022 p0040
  have p0042 :=
    @g_syl (.classMem D (syn_cwppreach F L)) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) p0001 p0041
  have p0043 :=
    @g_wppreachfwdrexvndv L D n G dv_cache_0001 dv_cache_0002 dv_cache_0029 hyp_wppreachprefixbidv_4 hyp_wppreachprefixbidv_5 hyp_wppreachprefixbidv_6 hyp_wppreachprefixbidv_7
  have p0044 :=
    @g_biimpri (.classMem D (syn_cwppreach G L)) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) p0043
  have p0045 :=
    @g_syl (.classMem D (syn_cwppreach F L)) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) (.classMem D (syn_cwppreach G L)) p0042 p0044
  have p0046 :=
    @g_wppreachfwdrexvndv L D n G dv_cache_0001 dv_cache_0002 dv_cache_0029 hyp_wppreachprefixbidv_4 hyp_wppreachprefixbidv_5 hyp_wppreachprefixbidv_6 hyp_wppreachprefixbidv_7
  have p0047 :=
    @g_biimpi (.classMem D (syn_cwppreach G L)) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) p0046
  have p0048 :=
    @g_finlewe
  have p0049 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) p0048
  have p0050 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))
  have p0051 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem D (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_wppreachprefixbidv_4 hyp_wppreachprefixbidv_5 hyp_wppreachprefixbidv_6
  have p0052 :=
    @g_elwpphitvndv L G D (.cv n)
  have p0053 :=
    Nominal.mp p0051 p0052
  have p0054 :=
    @g_biimpri (.classMem (.cv n) (syn_cwpphit G D L)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) p0053
  have p0055 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit G D L)) p0050 p0054
  have p0056 :=
    @g_rspe (.classMem (.cv n) (syn_cwpphit G D L)) n (syn_cnnc)
  have p0057 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit G D L))) (syn_wrex n (syn_cnnc) (.classMem (.cv n) (syn_cwpphit G D L))) p0055 p0056
  have p0058 :=
    @g_id (.classEq (.cv n) (.cv r))
  have p0059 :=
    @g_eleq1d (.classEq (.cv n) (.cv r)) (.cv n) (.cv r) (syn_cwpphit G D L) p0058
  have p0060_e00_recanon : Nominal.NPrf (.imp (.objEq n r) (syn_wb (.classMem (.cv n) (syn_cwpphit G D L)) (.classMem (.cv r) (syn_cwpphit G D L)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0059
  have p0060 :=
    @g_cbvrexv (.classMem (.cv n) (syn_cwpphit G D L)) (.classMem (.cv r) (syn_cwpphit G D L)) n r (syn_cnnc) dv_cache_0004 dv_cache_0005 dv_cache_0030 dv_cache_0031 p0060_e00_recanon
  have p0061 :=
    @g_biimpi (syn_wrex n (syn_cnnc) (.classMem (.cv n) (syn_cwpphit G D L))) (syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit G D L))) p0060
  have p0062 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) (syn_wrex n (syn_cnnc) (.classMem (.cv n) (syn_cwpphit G D L))) (syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit G D L))) p0057 p0061
  have p0063 :=
    @g_rexlimiva (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n))) (syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit G D L))) n (syn_cnnc) dv_cache_0032 p0062
  have p0064 :=
    @g_jca (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit G D L))) p0049 p0063
  have p0065 :=
    @g_elex G (syn_cfuns)
  have p0066 :=
    Nominal.mp hyp_wppreachprefixbidv_4 p0065
  have p0067 :=
    @g_wpphitminexvndv r L (syn_ckqrel (syn_clefin)) k q G D dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0033 dv_cache_0024 dv_cache_0034 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 p0066
  have p0068 :=
    @g_syl (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) (syn_wa (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wrex r (syn_cnnc) (.classMem (.cv r) (syn_cwpphit G D L)))) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) p0064 p0067
  have p0069 :=
    @g_wpphitprefixtransferpackdndv k F G D L q dv_cache_0013 dv_cache_0024 dv_cache_0016 dv_cache_0010 dv_cache_0021 hyp_wppreachprefixbidv_1 hyp_wppreachprefixbidv_2 hyp_wppreachprefixbidv_3 hyp_wppreachprefixbidv_4 hyp_wppreachprefixbidv_5 hyp_wppreachprefixbidv_6 hyp_wppreachprefixbidv_10 hyp_wppreachprefixbidv_11
  have p0070 :=
    @g_simpl (.classMem (.cv k) (syn_cwpphit F D L)) (.classEq (syn_cfv (syn_cfrec G D) (.cv k)) (syn_cfv (syn_cfrec F D) (.cv k)))
  have p0071 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv k) (syn_cwpphit F D L)) (.classEq (syn_cfv (syn_cfrec G D) (.cv k)) (syn_cfv (syn_cfrec F D) (.cv k)))) (.classMem (.cv k) (syn_cwpphit F D L)) p0069 p0070
  have p0072 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wppreachprefixbidv_1 hyp_wppreachprefixbidv_2 hyp_wppreachprefixbidv_3
  have p0073 :=
    @g_elwpphitvndv L F D (.cv k)
  have p0074 :=
    Nominal.mp p0072 p0073
  have p0075 :=
    @g_a1i (syn_wb (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k))))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) p0074
  have p0076 :=
    @g_biimpd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k)))) p0075
  have p0077 :=
    @g_mpd (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (.classMem (.cv k) (syn_cwpphit F D L)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k)))) p0071 p0076
  have p0078 :=
    @g_rspe (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k))) k (syn_cnnc)
  have p0079 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k)))) (syn_wrex k (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k)))) p0077 p0078
  have p0080 :=
    @g_id (.classEq (.cv k) (.cv n))
  have p0081 :=
    @g_fveq2d (.classEq (.cv k) (.cv n)) (.cv k) (.cv n) (syn_cfrec F D) p0080
  have p0082 :=
    @g_breq2d (.classEq (.cv k) (.cv n)) (syn_cfv (syn_cfrec F D) (.cv k)) (syn_cfv (syn_cfrec F D) (.cv n)) L (syn_clec) p0081
  have p0083_e00_recanon : Nominal.NPrf (.imp (.objEq k n) (syn_wb (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_clec syn_copab syn_cfv syn_cio syn_cuni syn_csn syn_cfrec syn_cclos1 syn_cint syn_cpprod syn_ctxp syn_cin syn_ccom syn_ccnv syn_c1st syn_cmpt syn_cvv syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0082
  have p0083 :=
    @g_cbvrexv (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k))) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) k n (syn_cnnc) dv_cache_0025 dv_cache_0004 dv_cache_0035 dv_cache_0036 p0083_e00_recanon
  have p0084 :=
    @g_biimpi (syn_wrex k (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k)))) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) p0083
  have p0085 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wrex k (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv k)))) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) p0079 p0084
  have p0086 :=
    @g_rexlimiva (syn_wa (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) k (syn_cnnc) dv_cache_0037 p0085
  have p0087 :=
    @g_syl (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k) (syn_cwpphit G D L)) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G D L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) p0068 p0086
  have p0088 :=
    @g_syl (.classMem D (syn_cwppreach G L)) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G D) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) p0047 p0087
  have p0089 :=
    @g_wppreachfwdrexvndv L D n F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wppreachprefixbidv_1 hyp_wppreachprefixbidv_2 hyp_wppreachprefixbidv_3 hyp_wppreachprefixbidv_7
  have p0090 :=
    @g_biimpri (.classMem D (syn_cwppreach F L)) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) p0089
  have p0091 :=
    @g_syl (.classMem D (syn_cwppreach G L)) (syn_wrex n (syn_cnnc) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (.classMem D (syn_cwppreach F L)) p0088 p0090
  have p0092 :=
    @g_impbii (.classMem D (syn_cwppreach F L)) (.classMem D (syn_cwppreach G L)) p0045 p0091
  exact p0092

#print axioms g_wppreachprefixbidv

end NFChoice.DirectNominalPrf.WPPReplay
