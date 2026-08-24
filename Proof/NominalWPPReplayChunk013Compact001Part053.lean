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
import NominalWPPReplayChunk013Compact001Part052

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

noncomputable def g_nclenc
    (A : Class) (B : Class) (f : Var) (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) (hyp_nclenc_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_nclenc_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wex f (syn_wf1 (.cv f) A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({f} : Finset Var)
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let g : Var := freshVar proofSupport 2
  let h : Var := freshVar proofSupport 3
  let i : Var := freshVar proofSupport 4
  let a : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_f : p ≠ f := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_p : f ≠ p :=
    Ne.symm fresh_p_ne_f
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_f : q ≠ f := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_q : f ≠ q :=
    Ne.symm fresh_q_ne_f
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_ne_f : g ≠ f := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_g : f ≠ g :=
    Ne.symm fresh_g_ne_f
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_h_not_B : h ∉ B.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_ne_f : h ≠ f := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_h : f ≠ h :=
    Ne.symm fresh_h_ne_f
  have fresh_i : i ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_i_not_A : i ∉ A.fv := by
    intro h
    exact fresh_i (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_i_not_B : i ∉ B.fv := by
    intro h
    exact fresh_i (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_i_ne_f : i ≠ f := by
    intro h
    exact fresh_i (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_i : f ≠ i :=
    Ne.symm fresh_i_ne_f
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_f : a ≠ f := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_a : f ≠ a :=
    Ne.symm fresh_a_ne_f
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_f : b ≠ f := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_b : f ≠ b :=
    Ne.symm fresh_b_ne_f
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have fresh_p_ne_g : p ≠ g := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_g_ne_p : g ≠ p :=
    Ne.symm fresh_p_ne_g
  have fresh_p_ne_h : p ≠ h := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_h_ne_p : h ≠ p :=
    Ne.symm fresh_p_ne_h
  have fresh_p_ne_i : p ≠ i := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_i_ne_p : i ≠ p :=
    Ne.symm fresh_p_ne_i
  have fresh_p_ne_a : p ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_a_ne_p : a ≠ p :=
    Ne.symm fresh_p_ne_a
  have fresh_p_ne_b : p ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_b_ne_p : b ≠ p :=
    Ne.symm fresh_p_ne_b
  have fresh_q_ne_g : q ≠ g := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_g_ne_q : g ≠ q :=
    Ne.symm fresh_q_ne_g
  have fresh_q_ne_h : q ≠ h := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_h_ne_q : h ≠ q :=
    Ne.symm fresh_q_ne_h
  have fresh_q_ne_i : q ≠ i := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_i_ne_q : i ≠ q :=
    Ne.symm fresh_q_ne_i
  have fresh_q_ne_a : q ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_a_ne_q : a ≠ q :=
    Ne.symm fresh_q_ne_a
  have fresh_q_ne_b : q ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_b_ne_q : b ≠ q :=
    Ne.symm fresh_q_ne_b
  have fresh_g_ne_h : g ≠ h := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_h_ne_g : h ≠ g :=
    Ne.symm fresh_g_ne_h
  have fresh_g_ne_i : g ≠ i := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_i_ne_g : i ≠ g :=
    Ne.symm fresh_g_ne_i
  have fresh_g_ne_a : g ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_a_ne_g : a ≠ g :=
    Ne.symm fresh_g_ne_a
  have fresh_g_ne_b : g ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_b_ne_g : b ≠ g :=
    Ne.symm fresh_g_ne_b
  have fresh_h_ne_i : h ≠ i := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_i_ne_h : i ≠ h :=
    Ne.symm fresh_h_ne_i
  have fresh_h_ne_a : h ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_a_ne_h : a ≠ h :=
    Ne.symm fresh_h_ne_a
  have fresh_h_ne_b : h ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_b_ne_h : b ≠ h :=
    Ne.symm fresh_h_ne_b
  have fresh_i_ne_a : i ≠ a := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_a_ne_i : a ≠ i :=
    Ne.symm fresh_i_ne_a
  have fresh_i_ne_b : i ≠ b := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_b_ne_i : b ≠ i :=
    Ne.symm fresh_i_ne_b
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : p ∉ ((syn_cnc A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0005 : p ≠ g := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show p ≠ g from (by exact fresh_p_ne_g))
  have dv_cache_0006 : q ≠ g := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show q ≠ g from (by exact fresh_q_ne_g))
  have dv_cache_0007 : h ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : h ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : i ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_i_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : i ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_i_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : i ∉ ((syn_wf1o (.cv h) (.cv p) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_i_ne_p, fresh_i_not_A, fresh_i_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : h ∉ ((syn_wf1o (.cv i) (.cv q) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_q, fresh_h_not_B, fresh_h_ne_i, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : f ∉ ((syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_i, fresh_f_ne_g, fresh_f_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : f ∉ ((syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))) A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, dv_B_f, fresh_f_ne_i, fresh_f_ne_g, fresh_f_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : h ∉ ((Wff.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_p, fresh_h_ne_q, fresh_h_ne_g, fresh_h_not_A, fresh_h_not_B, fresh_h_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : i ∉ ((Wff.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_i_ne_p, fresh_i_ne_q, fresh_i_ne_g, fresh_i_not_A, fresh_i_not_B, fresh_i_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : g ∉ ((syn_wex f (syn_wf1 (.cv f) A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, fresh_g_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : g ∉ ((syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_p, fresh_g_not_A, fresh_g_ne_q, fresh_g_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : q ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : p ∉ ((syn_wex f (syn_wf1 (.cv f) A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, fresh_p_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((syn_wex f (syn_wf1 (.cv f) A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, fresh_q_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : f ∉ ((Wff.classEq (.cv a) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_a, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : f ∉ ((Wff.classEq (.cv b) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_b, dv_B_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : a ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : b ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : a ∉ ((syn_wex f (syn_wf1 (.cv f) A (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, fresh_a_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : b ∉ ((syn_wex f (syn_wf1 (.cv f) A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_B, fresh_b_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0033 : a ≠ f := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show a ≠ f from (by exact fresh_a_ne_f))
  have dv_cache_0034 : b ≠ f := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show b ≠ f from (by exact fresh_b_ne_f))
  have p0000 :=
    @g_ncelncsi A hyp_nclenc_1
  have p0001 :=
    @g_ncelncsi B hyp_nclenc_2
  have p0002 :=
    @g_dflec3 g (syn_cnc A) (syn_cnc B) p q dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    @g_mp2an (.classMem (syn_cnc A) (syn_cncs)) (.classMem (syn_cnc B) (syn_cncs)) (syn_wb (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wrex p (syn_cnc A) (syn_wrex q (syn_cnc B) (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q)))))) p0000 p0001 p0002
  have p0004 :=
    @g_elnc (.cv p) A
  have p0005 :=
    @g_bren (.cv p) A h dv_cache_0007 dv_cache_0008
  have p0006 :=
    @g_bitri (.classMem (.cv p) (syn_cnc A)) (syn_wbr (.cv p) (syn_cen) A) (syn_wex h (syn_wf1o (.cv h) (.cv p) A)) p0004 p0005
  have p0007 :=
    @g_elnc (.cv q) B
  have p0008 :=
    @g_bren (.cv q) B i dv_cache_0009 dv_cache_0010
  have p0009 :=
    @g_bitri (.classMem (.cv q) (syn_cnc B)) (syn_wbr (.cv q) (syn_cen) B) (syn_wex i (syn_wf1o (.cv i) (.cv q) B)) p0007 p0008
  have p0010 :=
    @g_anbi12i (.classMem (.cv p) (syn_cnc A)) (syn_wex h (syn_wf1o (.cv h) (.cv p) A)) (.classMem (.cv q) (syn_cnc B)) (syn_wex i (syn_wf1o (.cv i) (.cv q) B)) p0006 p0009
  have p0011 :=
    @g_eeanv (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B) h i dv_cache_0011 dv_cache_0012
  have p0012 :=
    @g_bitr4i (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B))) (syn_wa (syn_wex h (syn_wf1o (.cv h) (.cv p) A)) (syn_wex i (syn_wf1o (.cv i) (.cv q) B))) (syn_wex h (syn_wex i (syn_wa (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B)))) p0010 p0011
  have p0013 :=
    @g_f1of1 (.cv q) B (.cv i)
  have p0014 :=
    @g_n_3ad2ant2 (syn_wf1o (.cv i) (.cv q) B) (syn_wf1o (.cv h) (.cv p) A) (syn_wf1 (.cv i) (.cv q) B) (syn_wf1 (.cv g) (.cv p) (.cv q)) p0013
  have p0015 :=
    @g_simp3 (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B) (syn_wf1 (.cv g) (.cv p) (.cv q))
  have p0016 :=
    @g_f1co (.cv p) (.cv q) B (.cv i) (.cv g)
  have p0017 :=
    @g_syl2anc (syn_w3a (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B) (syn_wf1 (.cv g) (.cv p) (.cv q))) (syn_wf1 (.cv i) (.cv q) B) (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wf1 (syn_ccom (.cv i) (.cv g)) (.cv p) B) p0014 p0015 p0016
  have p0018 :=
    @g_f1ocnv (.cv p) A (.cv h)
  have p0019 :=
    @g_f1of1 A (.cv p) (syn_ccnv (.cv h))
  have p0020 :=
    @g_syl (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (syn_ccnv (.cv h)) A (.cv p)) (syn_wf1 (syn_ccnv (.cv h)) A (.cv p)) p0018 p0019
  have p0021 :=
    @g_n_3ad2ant1 (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B) (syn_wf1 (syn_ccnv (.cv h)) A (.cv p)) (syn_wf1 (.cv g) (.cv p) (.cv q)) p0020
  have p0022 :=
    @g_f1co A (.cv p) B (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))
  have p0023 :=
    @g_syl2anc (syn_w3a (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B) (syn_wf1 (.cv g) (.cv p) (.cv q))) (syn_wf1 (syn_ccom (.cv i) (.cv g)) (.cv p) B) (syn_wf1 (syn_ccnv (.cv h)) A (.cv p)) (syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))) A B) p0017 p0021 p0022
  have p0024 :=
    @g_vex i
  have p0025 :=
    @g_vex g
  have p0026 :=
    @g_coex (.cv i) (.cv g) p0024 p0025
  have p0027 :=
    @g_vex h
  have p0028 :=
    @g_cnvex (.cv h) p0027
  have p0029 :=
    @g_coex (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)) p0026 p0028
  have p0030 :=
    @g_f1eq1 A B (.cv f) (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h)))
  have p0031 :=
    @g_spcev (syn_wf1 (.cv f) A B) (syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))) A B) f (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))) dv_cache_0013 dv_cache_0014 p0029 p0030
  have p0032 :=
    @g_syl (syn_w3a (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B) (syn_wf1 (.cv g) (.cv p) (.cv q))) (syn_wf1 (syn_ccom (syn_ccom (.cv i) (.cv g)) (syn_ccnv (.cv h))) A B) (syn_wex f (syn_wf1 (.cv f) A B)) p0023 p0031
  have p0033 :=
    @g_n_3expia (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B) (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B)) p0032
  have p0034 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B)) (.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B))) h i dv_cache_0015 dv_cache_0016 p0033
  have p0035 :=
    @g_sylbi (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B))) (syn_wex h (syn_wex i (syn_wa (syn_wf1o (.cv h) (.cv p) A) (syn_wf1o (.cv i) (.cv q) B)))) (.imp (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B))) p0012 p0034
  have p0036 :=
    @g_exlimdv (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B))) (syn_wf1 (.cv g) (.cv p) (.cv q)) (syn_wex f (syn_wf1 (.cv f) A B)) g dv_cache_0017 dv_cache_0018 p0035
  have p0037 :=
    @g_rexlimivv (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q))) (syn_wex f (syn_wf1 (.cv f) A B)) p q (syn_cnc A) (syn_cnc B) dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0004 p0036
  have p0038 :=
    @g_sylbi (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wrex p (syn_cnc A) (syn_wrex q (syn_cnc B) (syn_wex g (syn_wf1 (.cv g) (.cv p) (.cv q))))) (syn_wex f (syn_wf1 (.cv f) A B)) p0003 p0037
  have p0039 :=
    @g_ncid A hyp_nclenc_1
  have p0040 :=
    @g_ncid B hyp_nclenc_2
  have p0041 :=
    @g_f1eq2 (.cv a) A (.cv b) (.cv f)
  have p0042 :=
    @g_exbidv (.classEq (.cv a) A) (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wf1 (.cv f) A (.cv b)) f dv_cache_0022 p0041
  have p0043 :=
    @g_f1eq3 (.cv b) B A (.cv f)
  have p0044 :=
    @g_exbidv (.classEq (.cv b) B) (syn_wf1 (.cv f) A (.cv b)) (syn_wf1 (.cv f) A B) f dv_cache_0023 p0043
  have p0045 :=
    @g_rspc2ev (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))) (syn_wex f (syn_wf1 (.cv f) A B)) (syn_wex f (syn_wf1 (.cv f) A (.cv b))) a b A B (syn_cnc A) (syn_cnc B) dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 p0042 p0044
  have p0046 :=
    @g_mp3an12 (.classMem A (syn_cnc A)) (.classMem B (syn_cnc B)) (syn_wex f (syn_wf1 (.cv f) A B)) (syn_wrex a (syn_cnc A) (syn_wrex b (syn_cnc B) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))) p0039 p0040 p0045
  have p0047 :=
    @g_dflec3 f (syn_cnc A) (syn_cnc B) a b dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0032 dv_cache_0033 dv_cache_0034
  have p0048 :=
    @g_mp2an (.classMem (syn_cnc A) (syn_cncs)) (.classMem (syn_cnc B) (syn_cncs)) (syn_wb (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wrex a (syn_cnc A) (syn_wrex b (syn_cnc B) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))) p0000 p0001 p0047
  have p0049 :=
    @g_sylibr (syn_wex f (syn_wf1 (.cv f) A B)) (syn_wrex a (syn_cnc A) (syn_wrex b (syn_cnc B) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))) (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) p0046 p0048
  have p0050 :=
    @g_impbii (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wex f (syn_wf1 (.cv f) A B)) p0038 p0049
  exact p0050

#print axioms g_nclenc

end NFChoice.DirectNominalPrf.WPPReplay
