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
import NominalWPPReplayChunk013Compact001Part056

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

noncomputable def g_letc
    (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc N))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({p} : Finset Var)
  let q : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  let c : Var := freshVar proofSupport 3
  let x : Var := freshVar proofSupport 4
  let y : Var := freshVar proofSupport 5
  let n : Var := freshVar proofSupport 6
  let m : Var := freshVar proofSupport 7
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_p : a ≠ p := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_a : p ≠ a :=
    Ne.symm fresh_a_ne_p
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_p : b ≠ p := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_b : p ≠ b :=
    Ne.symm fresh_b_ne_p
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_c_not_M : c ∉ M.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_c_not_N : c ∉ N.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_ne_p : c ≠ p := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_c : p ≠ c :=
    Ne.symm fresh_c_ne_p
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_p : x ≠ p := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_p : y ≠ p := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_p : n ≠ p := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_n : p ≠ n :=
    Ne.symm fresh_n_ne_p
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_ne_p : m ≠ p := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_m : p ≠ m :=
    Ne.symm fresh_m_ne_p
  have fresh_q_ne_a : q ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_q : a ≠ q :=
    Ne.symm fresh_q_ne_a
  have fresh_q_ne_b : q ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_q : b ≠ q :=
    Ne.symm fresh_q_ne_b
  have fresh_q_ne_c : q ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_c_ne_q : c ≠ q :=
    Ne.symm fresh_q_ne_c
  have fresh_q_ne_x : q ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_ne_y : q ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_y_ne_q : y ≠ q :=
    Ne.symm fresh_q_ne_y
  have fresh_q_ne_n : q ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_n_ne_q : n ≠ q :=
    Ne.symm fresh_q_ne_n
  have fresh_q_ne_m : q ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_m_ne_q : m ≠ q :=
    Ne.symm fresh_q_ne_m
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_n : a ≠ n := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_n_ne_a : n ≠ a :=
    Ne.symm fresh_a_ne_n
  have fresh_a_ne_m : a ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_m_ne_a : m ≠ a :=
    Ne.symm fresh_a_ne_m
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_ne_n : b ≠ n := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_n_ne_b : n ≠ b :=
    Ne.symm fresh_b_ne_n
  have fresh_b_ne_m : b ≠ m := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_m_ne_b : m ≠ b :=
    Ne.symm fresh_b_ne_m
  have fresh_c_ne_x : c ≠ x := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_x_ne_c : x ≠ c :=
    Ne.symm fresh_c_ne_x
  have fresh_c_ne_y : c ≠ y := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_y_ne_c : y ≠ c :=
    Ne.symm fresh_c_ne_y
  have fresh_c_ne_n : c ≠ n := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_n_ne_c : n ≠ c :=
    Ne.symm fresh_c_ne_n
  have fresh_c_ne_m : c ≠ m := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_m_ne_c : m ≠ c :=
    Ne.symm fresh_c_ne_m
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_n : x ≠ n := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_n_ne_x : n ≠ x :=
    Ne.symm fresh_x_ne_n
  have fresh_x_ne_m : x ≠ m := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    Ne.symm fresh_x_ne_m
  have fresh_y_ne_n : y ≠ n := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_n_ne_y : n ≠ y :=
    Ne.symm fresh_y_ne_n
  have fresh_y_ne_m : y ≠ m := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_m_ne_y : m ≠ y :=
    Ne.symm fresh_y_ne_m
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have dv_cache_0001 : q ∉ (M).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_ctc N)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : c ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((Wff.classEq (.cv q) (syn_cnc (.cv c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_q, fresh_a_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((Wff.classEq (.cv q) (syn_cnc (.cv c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_q, fresh_b_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((Wff.classEq M (syn_cnc (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_M, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : c ∉ ((Wff.classEq M (syn_cnc (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_M, fresh_c_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((Wff.classEq N (syn_cnc (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : c ∉ ((Wff.classEq N (syn_cnc (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_N, fresh_c_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0013 : a ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show a ≠ c from (by exact fresh_a_ne_c))
  have dv_cache_0014 : x ∉ ((syn_cpw1 (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cpw1 (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_cnc (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_cnc (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_cnc (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((syn_cnc (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0021 : n ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : m ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : n ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : m ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : n ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : m ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : n ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have dv_cache_0028 : p ∉ ((syn_cnc (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : p ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : p ∉ ((Wff.classEq (syn_cnc (.cv a)) (syn_cnc (syn_cpw1 (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_a, fresh_p_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : n ∉ ((Wff.imp (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, fresh_n_ne_a, fresh_n_ne_y, fresh_n_ne_c, fresh_n_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : m ∉ ((Wff.imp (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_x, fresh_m_ne_a, fresh_m_ne_y, fresh_m_ne_c, fresh_m_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : x ∉ ((syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : y ∉ ((syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : p ∉ ((Wff.classEq M (syn_cnc (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_p, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : c ∉ ((Wff.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_N, fresh_c_not_M, fresh_c_ne_q, fresh_c_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : a ∉ ((Wff.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, fresh_a_not_M, fresh_a_ne_q, fresh_a_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : b ∉ ((Wff.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_N, fresh_b_not_M, fresh_b_ne_q, fresh_b_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : q ∉ ((syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0040 : q ∉ ((syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_tccl N
  have p0001 :=
    @g_dflec2 M (syn_ctc N) q dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_sylan2 (.classMem N (syn_cncs)) (.classMem M (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) (syn_wb (syn_wbr M (syn_clec) (syn_ctc N)) (syn_wrex q (syn_cncs) (.classEq (syn_ctc N) (syn_cplc M (.cv q))))) p0000 p0001
  have p0003 :=
    @g_elncs a M dv_cache_0003
  have p0004 :=
    @g_elncs b N dv_cache_0004
  have p0005 :=
    @g_elncs c (.cv q) dv_cache_0005
  have p0006 :=
    @g_n_3anbi123i (.classMem M (syn_cncs)) (syn_wex a (.classEq M (syn_cnc (.cv a)))) (.classMem N (syn_cncs)) (syn_wex b (.classEq N (syn_cnc (.cv b)))) (.classMem (.cv q) (syn_cncs)) (syn_wex c (.classEq (.cv q) (syn_cnc (.cv c)))) p0003 p0004 p0005
  have p0007 :=
    @g_eeeanv (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))) (.classEq (.cv q) (syn_cnc (.cv c))) a b c dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0008 :=
    @g_bitr4i (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (.classMem (.cv q) (syn_cncs))) (syn_w3a (syn_wex a (.classEq M (syn_cnc (.cv a)))) (syn_wex b (.classEq N (syn_cnc (.cv b)))) (syn_wex c (.classEq (.cv q) (syn_cnc (.cv c))))) (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))) (.classEq (.cv q) (syn_cnc (.cv c))))))) p0006 p0007
  have p0009 :=
    @g_eqcom (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))
  have p0010 :=
    @g_vex a
  have p0011 :=
    @g_ncelncsi (.cv a) p0010
  have p0012 :=
    @g_vex c
  have p0013 :=
    @g_ncelncsi (.cv c) p0012
  have p0014 :=
    @g_ncaddccl (syn_cnc (.cv a)) (syn_cnc (.cv c))
  have p0015 :=
    @g_mp2an (.classMem (syn_cnc (.cv a)) (syn_cncs)) (.classMem (syn_cnc (.cv c)) (syn_cncs)) (.classMem (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))) (syn_cncs)) p0011 p0013 p0014
  have p0016 :=
    @g_ncseqnc (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))) (syn_cpw1 (.cv b))
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_bitri (.classEq (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))) (.classEq (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))) (syn_cnc (syn_cpw1 (.cv b)))) (.classMem (syn_cpw1 (.cv b)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))) p0009 p0017
  have p0019 :=
    @g_eladdc (syn_cpw1 (.cv b)) (syn_cnc (.cv a)) (syn_cnc (.cv c)) x y dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0020 :=
    @g_vex x
  have p0021 :=
    @g_vex y
  have p0022 :=
    @g_pw1equn n m (.cv x) (.cv y) (.cv b) dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 p0020 p0021
  have p0023 :=
    @g_eleq1 (.cv x) (syn_cpw1 (.cv n)) (syn_cnc (.cv a))
  have p0024 :=
    @g_eleq1 (.cv y) (syn_cpw1 (.cv m)) (syn_cnc (.cv c))
  have p0025 :=
    @g_bi2anan9 (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (syn_cpw1 (.cv n)) (syn_cnc (.cv a))) (.classEq (.cv y) (syn_cpw1 (.cv m))) (.classMem (.cv y) (syn_cnc (.cv c))) (.classMem (syn_cpw1 (.cv m)) (syn_cnc (.cv c))) p0023 p0024
  have p0026 :=
    @g_ineq12 (.cv x) (syn_cpw1 (.cv n)) (.cv y) (syn_cpw1 (.cv m))
  have p0027 :=
    @g_eqeq1d (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m)))) (syn_cin (.cv x) (.cv y)) (syn_cin (syn_cpw1 (.cv n)) (syn_cpw1 (.cv m))) (syn_c0) p0026
  have p0028 :=
    @g_anbi12d (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m)))) (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c)))) (syn_wa (.classMem (syn_cpw1 (.cv n)) (syn_cnc (.cv a))) (.classMem (syn_cpw1 (.cv m)) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) (.classEq (syn_cin (syn_cpw1 (.cv n)) (syn_cpw1 (.cv m))) (syn_c0)) p0025 p0027
  have p0029 :=
    @g_ncseqnc (syn_cnc (.cv a)) (syn_cpw1 (.cv n))
  have p0030 :=
    Nominal.mp p0011 p0029
  have p0031 :=
    @g_vex n
  have p0032 :=
    @g_ncelncsi (.cv n) p0031
  have p0033 :=
    @g_tceq (.cv p) (syn_cnc (.cv n))
  have p0034 :=
    @g_tcnc (.cv n) p0031
  have p0035 :=
    @g_syl6eq (.classEq (.cv p) (syn_cnc (.cv n))) (syn_ctc (.cv p)) (syn_ctc (syn_cnc (.cv n))) (syn_cnc (syn_cpw1 (.cv n))) p0033 p0034
  have p0036 :=
    @g_eqeq2d (.classEq (.cv p) (syn_cnc (.cv n))) (syn_ctc (.cv p)) (syn_cnc (syn_cpw1 (.cv n))) (syn_cnc (.cv a)) p0035
  have p0037 :=
    @g_rspcev (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))) (.classEq (syn_cnc (.cv a)) (syn_cnc (syn_cpw1 (.cv n)))) p (syn_cnc (.cv n)) (syn_cncs) dv_cache_0028 dv_cache_0029 dv_cache_0030 p0036
  have p0038 :=
    @g_mpan (.classMem (syn_cnc (.cv n)) (syn_cncs)) (.classEq (syn_cnc (.cv a)) (syn_cnc (syn_cpw1 (.cv n)))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0032 p0037
  have p0039 :=
    @g_sylbir (.classMem (syn_cpw1 (.cv n)) (syn_cnc (.cv a))) (.classEq (syn_cnc (.cv a)) (syn_cnc (syn_cpw1 (.cv n)))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0030 p0038
  have p0040 :=
    @g_ad2antrr (.classMem (syn_cpw1 (.cv n)) (syn_cnc (.cv a))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) (.classMem (syn_cpw1 (.cv m)) (syn_cnc (.cv c))) (.classEq (syn_cin (syn_cpw1 (.cv n)) (syn_cpw1 (.cv m))) (syn_c0)) p0039
  have p0041 :=
    @g_syl6bi (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m)))) (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv n)) (syn_cnc (.cv a))) (.classMem (syn_cpw1 (.cv m)) (syn_cnc (.cv c)))) (.classEq (syn_cin (syn_cpw1 (.cv n)) (syn_cpw1 (.cv m))) (syn_c0))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0028 p0040
  have p0042 :=
    @g_n_3adant1 (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m))) (.imp (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))))) (.classEq (.cv b) (syn_cun (.cv n) (.cv m))) p0041
  have p0043 :=
    @g_exlimivv (syn_w3a (.classEq (.cv b) (syn_cun (.cv n) (.cv m))) (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m)))) (.imp (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))))) n m dv_cache_0031 dv_cache_0032 p0042
  have p0044 :=
    @g_com12 (syn_wex n (syn_wex m (syn_w3a (.classEq (.cv b) (syn_cun (.cv n) (.cv m))) (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m)))))) (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0043
  have p0045 :=
    @g_syl5bi (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv x) (.cv y))) (syn_wex n (syn_wex m (syn_w3a (.classEq (.cv b) (syn_cun (.cv n) (.cv m))) (.classEq (.cv x) (syn_cpw1 (.cv n))) (.classEq (.cv y) (syn_cpw1 (.cv m)))))) (syn_wa (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0022 p0044
  have p0046 :=
    @g_expimpd (syn_wa (.classMem (.cv x) (syn_cnc (.cv a))) (.classMem (.cv y) (syn_cnc (.cv c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv x) (.cv y))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0045
  have p0047 :=
    @g_rexlimivv (syn_wa (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv x) (.cv y)))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) x y (syn_cnc (.cv a)) (syn_cnc (.cv c)) dv_cache_0017 dv_cache_0033 dv_cache_0034 dv_cache_0020 p0046
  have p0048 :=
    @g_sylbi (.classMem (syn_cpw1 (.cv b)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))) (syn_wrex x (syn_cnc (.cv a)) (syn_wrex y (syn_cnc (.cv c)) (syn_wa (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) (.classEq (syn_cpw1 (.cv b)) (syn_cun (.cv x) (.cv y)))))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0019 p0047
  have p0049 :=
    @g_sylbi (.classEq (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))) (.classMem (syn_cpw1 (.cv b)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0018 p0048
  have p0050 :=
    @g_tceq N (syn_cnc (.cv b))
  have p0051 :=
    @g_vex b
  have p0052 :=
    @g_tcnc (.cv b) p0051
  have p0053 :=
    @g_syl6eq (.classEq N (syn_cnc (.cv b))) (syn_ctc N) (syn_ctc (syn_cnc (.cv b))) (syn_cnc (syn_cpw1 (.cv b))) p0050 p0052
  have p0054 :=
    @g_n_3ad2ant2 (.classEq N (syn_cnc (.cv b))) (.classEq M (syn_cnc (.cv a))) (.classEq (syn_ctc N) (syn_cnc (syn_cpw1 (.cv b)))) (.classEq (.cv q) (syn_cnc (.cv c))) p0053
  have p0055 :=
    @g_addceq12 M (.cv q) (syn_cnc (.cv a)) (syn_cnc (.cv c))
  have p0056 :=
    @g_n_3adant2 (.classEq M (syn_cnc (.cv a))) (.classEq (.cv q) (syn_cnc (.cv c))) (.classEq (syn_cplc M (.cv q)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))) (.classEq N (syn_cnc (.cv b))) p0055
  have p0057 :=
    @g_eqeq12d (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))) (.classEq (.cv q) (syn_cnc (.cv c)))) (syn_ctc N) (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc M (.cv q)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c))) p0054 p0056
  have p0058 :=
    @g_eqeq1 M (syn_cnc (.cv a)) (syn_ctc (.cv p))
  have p0059 :=
    @g_rexbidv (.classEq M (syn_cnc (.cv a))) (.classEq M (syn_ctc (.cv p))) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))) p (syn_cncs) dv_cache_0035 p0058
  have p0060 :=
    @g_n_3ad2ant1 (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))) (syn_wb (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))))) (.classEq (.cv q) (syn_cnc (.cv c))) p0059
  have p0061 :=
    @g_imbi12d (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))) (.classEq (.cv q) (syn_cnc (.cv c)))) (.classEq (syn_ctc N) (syn_cplc M (.cv q))) (.classEq (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p)))) p0057 p0060
  have p0062 :=
    @g_mpbiri (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))) (.classEq (.cv q) (syn_cnc (.cv c)))) (.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))) (.imp (.classEq (syn_cnc (syn_cpw1 (.cv b))) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (.cv c)))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv a)) (syn_ctc (.cv p))))) p0049 p0061
  have p0063 :=
    @g_exlimiv (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))) (.classEq (.cv q) (syn_cnc (.cv c)))) (.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))) c dv_cache_0036 p0062
  have p0064 :=
    @g_exlimivv (syn_wex c (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))) (.classEq (.cv q) (syn_cnc (.cv c))))) (.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))) a b dv_cache_0037 dv_cache_0038 p0063
  have p0065 :=
    @g_sylbi (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (.classMem (.cv q) (syn_cncs))) (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b))) (.classEq (.cv q) (syn_cnc (.cv c))))))) (.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))) p0008 p0064
  have p0066 :=
    @g_n_3expa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (.classMem (.cv q) (syn_cncs)) (.imp (.classEq (syn_ctc N) (syn_cplc M (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p))))) p0065
  have p0067 :=
    @g_rexlimdva (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classEq (syn_ctc N) (syn_cplc M (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))) q (syn_cncs) dv_cache_0039 dv_cache_0040 p0066
  have p0068 :=
    @g_sylbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr M (syn_clec) (syn_ctc N)) (syn_wrex q (syn_cncs) (.classEq (syn_ctc N) (syn_cplc M (.cv q)))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))) p0002 p0067
  have p0069 :=
    @g_n_3impia (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc N)) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (.cv p)))) p0068
  exact p0069

#print axioms g_letc

end NFChoice.DirectNominalPrf.WPPReplay
