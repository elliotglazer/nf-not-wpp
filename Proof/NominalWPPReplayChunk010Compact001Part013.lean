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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk010Compact001Part012

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

noncomputable def g_sfindbl
    (A : Class) (n : Var) (M : Class) (dv_M_n : n ∉ M.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 A) (syn_cplc M (syn_c1c)))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))) := by
  let proofSupport : Finset Var := A.fv ∪ ({n} : Finset Var) ∪ M.fv
  let b : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let k : Var := freshVar proofSupport 4
  let a : Var := freshVar proofSupport 5
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_b : n ≠ b :=
    Ne.symm fresh_b_ne_n
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_ne_n : x ≠ n := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_x : n ≠ x :=
    Ne.symm fresh_x_ne_n
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_n : y ≠ n := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_y : n ≠ y :=
    Ne.symm fresh_y_ne_n
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_n : z ≠ n := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_z : n ≠ z :=
    Ne.symm fresh_z_ne_n
  have fresh_z_not_M : z ∉ M.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_k_not_A : k ∉ A.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_ne_n : k ≠ n := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_k : n ≠ k :=
    Ne.symm fresh_k_ne_n
  have fresh_k_not_M : k ∉ M.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_a : n ≠ a :=
    Ne.symm fresh_a_ne_n
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_ne_z : b ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_b : z ≠ b :=
    Ne.symm fresh_b_ne_z
  have fresh_b_ne_k : b ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_k_ne_b : k ≠ b :=
    Ne.symm fresh_b_ne_k
  have fresh_b_ne_a : b ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_a_ne_b : a ≠ b :=
    Ne.symm fresh_b_ne_a
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_k : x ≠ k := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_k_ne_x : k ≠ x :=
    Ne.symm fresh_x_ne_k
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_k : y ≠ k := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_k_ne_y : k ≠ y :=
    Ne.symm fresh_y_ne_k
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_z_ne_k : z ≠ k := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_k_ne_z : k ≠ z :=
    Ne.symm fresh_z_ne_k
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_k_ne_a : k ≠ a := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_a_ne_k : a ≠ k :=
    Ne.symm fresh_k_ne_a
  have dv_cache_0001 : b ∉ ((syn_cpw1 A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cpw1 A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0005 : y ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0012 : k ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ ((syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_not_M, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : a ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((syn_cun (.cv y) (syn_csn (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((syn_wa (.classMem (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc M (syn_c1c))) (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, fresh_a_not_M, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((syn_cplc M (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : a ∉ ((syn_cplc (.cv n) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : n ∉ ((syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_y, dv_M_n, fresh_n_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : k ∉ ((syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_M, fresh_k_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : k ∉ ((syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_M, fresh_k_ne_y, fresh_k_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : y ∉ ((syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, fresh_y_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : z ∉ ((syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_M, fresh_z_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : y ∉ ((syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, fresh_y_ne_b, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : z ∉ ((syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_M, fresh_z_ne_b, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : x ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : b ∉ ((syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_M, fresh_b_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : x ∉ ((syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : b ∉ ((Wff.classMem M (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : x ∉ ((Wff.classMem M (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elsuc x (syn_cpw1 A) M b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @g_vex b
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_pw1eqadj y z (.cv b) (.cv x) A dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0001 p0002
  have p0004 :=
    @g_eleq1 (.cv b) (syn_cpw1 (.cv y)) M
  have p0005 :=
    @g_adantr (.classEq (.cv b) (syn_cpw1 (.cv y))) (syn_wb (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv y)) M)) (.classEq (.cv x) (syn_csn (.cv z))) p0004
  have p0006 :=
    @g_compleq (.cv b) (syn_cpw1 (.cv y))
  have p0007 :=
    @g_eleq12 (.cv x) (syn_csn (.cv z)) (syn_ccompl (.cv b)) (syn_ccompl (syn_cpw1 (.cv y)))
  have p0008 :=
    @g_snex (.cv z)
  have p0009 :=
    @g_elcompl (syn_csn (.cv z)) (syn_cpw1 (.cv y)) p0008
  have p0010 :=
    @g_snelpw1 (.cv z) (.cv y)
  have p0011_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0010
  have p0011 :=
    @g_xchbinx (.classMem (syn_csn (.cv z)) (syn_ccompl (syn_cpw1 (.cv y)))) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) (.objMem z y) p0009 p0011_e01_recanon
  have p0012 :=
    @g_syl6bb (syn_wa (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (syn_ccompl (.cv b)) (syn_ccompl (syn_cpw1 (.cv y))))) (.classMem (.cv x) (syn_ccompl (.cv b))) (.classMem (syn_csn (.cv z)) (syn_ccompl (syn_cpw1 (.cv y)))) (.neg (.objMem z y)) p0007 p0011
  have p0013 :=
    @g_sylan2 (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (syn_ccompl (.cv b)) (syn_ccompl (syn_cpw1 (.cv y)))) (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem z y))) p0006 p0012
  have p0014 :=
    @g_ancoms (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv b) (syn_cpw1 (.cv y))) (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem z y))) p0013
  have p0015 :=
    @g_anbi12d (syn_wa (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z)))) (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv y)) M) (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem z y)) p0005 p0014
  have p0016 :=
    @g_anbi2d (syn_wa (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z)))) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (.classMem M (syn_cnnc)) p0015
  have p0017 :=
    @g_ncfinlower (.cv y) (.cv y) k M dv_cache_0012 dv_cache_0012
  have p0018_e00_recanon : Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw1 (.cv y)) M)) (syn_wrex k (syn_cnnc) (syn_wa (.objMem y k) (.objMem y k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_wrex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0017
  have p0018 :=
    @g_n_3anidm23 (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv y)) M) (syn_wrex k (syn_cnnc) (syn_wa (.objMem y k) (.objMem y k))) p0018_e00_recanon
  have p0019 :=
    @g_adantrr (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv y)) M) (syn_wrex k (syn_cnnc) (syn_wa (.objMem y k) (.objMem y k))) (.neg (.objMem z y)) p0018
  have p0020 :=
    @g_simp3l (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))
  have p0021 :=
    @g_simp3rr (.objMem y k) (.objMem y k) (.classMem (.cv k) (syn_cnnc)) (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
  have p0022 :=
    @g_nnpweq (.cv y) (.cv y) n (.cv k) dv_cache_0013 dv_cache_0013 dv_cache_0014
  have p0023_e03_recanon : Nominal.NPrf (.imp (syn_w3a (.classMem (.cv k) (syn_cnnc)) (.objMem y k) (.objMem y k)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_wrex syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0022
  have p0023 :=
    @g_syl3anc (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (.classMem (.cv k) (syn_cnnc)) (.objMem y k) (.objMem y k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n)))) p0020 p0021 p0021 p0023_e03_recanon
  have p0024 :=
    @g_simpl1 (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))
  have p0025 :=
    @g_simprl (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n)))
  have p0026 :=
    @g_simpl2l (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)) (.classMem M (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))
  have p0027 :=
    @g_simprrr (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))
  have p0028 :=
    @g_vex y
  have p0029 :=
    @g_pw1eq (.cv a) (.cv y)
  have p0030_e00_recanon : Nominal.NPrf (.imp (.objEq a y) (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0029
  have p0030 :=
    @g_eleq1d (.objEq a y) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv y)) M p0030_e00_recanon
  have p0031 :=
    @g_pweq (.cv a) (.cv y)
  have p0032_e00_recanon : Nominal.NPrf (.imp (.objEq a y) (.classEq (syn_cpw (.cv a)) (syn_cpw (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0031
  have p0032 :=
    @g_eleq1d (.objEq a y) (syn_cpw (.cv a)) (syn_cpw (.cv y)) (.cv n) p0032_e00_recanon
  have p0033 :=
    @g_anbi12d (.objEq a y) (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n)) p0030 p0032
  have p0034_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (.cv y)) (syn_wb (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) (.cv n))) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0033
  have p0034 :=
    @g_spcev (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) (.cv n))) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) (.cv n))) a (.cv y) dv_cache_0015 dv_cache_0016 p0028 p0034_e01_recanon
  have p0035 :=
    @g_syl2anc (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) (.cv n)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) (.cv n)))) p0026 p0027 p0034
  have p0036 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M (.cv n) a dv_cache_0017 dv_cache_0018
  have p0037 :=
    @g_syl3anbrc (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (.classMem M (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) (.cv n)))) (syn_wsfin M (.cv n)) p0024 p0025 p0035 p0036
  have p0038 :=
    @g_peano2 M
  have p0039 :=
    @g_syl (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (.classMem M (syn_cnnc)) (.classMem (syn_cplc M (syn_c1c)) (syn_cnnc)) p0024 p0038
  have p0040 :=
    @g_nncaddccl (.cv n) (.cv n)
  have p0041 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0040
  have p0042 :=
    @g_syl (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0025 p0041
  have p0043 :=
    @g_pw1un (.cv y) (syn_csn (.cv z))
  have p0044 :=
    @g_vex z
  have p0045 :=
    @g_pw1sn (.cv z) p0044
  have p0046 :=
    @g_uneq2i (syn_cpw1 (syn_csn (.cv z))) (syn_csn (syn_csn (.cv z))) (syn_cpw1 (.cv y)) p0045
  have p0047 :=
    @g_eqtri (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cun (syn_cpw1 (.cv y)) (syn_cpw1 (syn_csn (.cv z)))) (syn_cun (syn_cpw1 (.cv y)) (syn_csn (syn_csn (.cv z)))) p0043 p0046
  have p0048 :=
    @g_simpl2r (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)) (.classMem M (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))
  have p0049_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0010
  have p0049 :=
    @g_sylnibr (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (.objMem z y) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) p0048 p0049_e01_recanon
  have p0050 :=
    @g_elsuci (syn_cpw1 (.cv y)) M (syn_csn (.cv z)) p0008
  have p0051 :=
    @g_syl2anc (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (.classMem (syn_cpw1 (.cv y)) M) (.neg (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y)))) (.classMem (syn_cun (syn_cpw1 (.cv y)) (syn_csn (syn_csn (.cv z)))) (syn_cplc M (syn_c1c))) p0026 p0049 p0050
  have p0052 :=
    @g_syl5eqel (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cun (syn_cpw1 (.cv y)) (syn_csn (syn_csn (.cv z)))) (syn_cplc M (syn_c1c)) p0047 p0051
  have p0053 :=
    @g_simpl3l (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)) (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))
  have p0054 :=
    @g_adantr (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (.objMem y k) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n)))) p0021
  have p0055 :=
    @g_elcompl (.cv z) (.cv y) p0044
  have p0056_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv z) (syn_ccompl (.cv y))) (.neg (.objMem z y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0055
  have p0056 :=
    @g_sylibr (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (.neg (.objMem z y)) (.classMem (.cv z) (syn_ccompl (.cv y))) p0048 p0056_e01_recanon
  have p0057 :=
    @g_nnadjoinpw (.cv y) (.cv k) (.cv n) (.cv z)
  have p0058_e05_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (.objMem y k) (.classMem (.cv z) (syn_ccompl (.cv y)))) (.classMem (syn_cpw (.cv y)) (.cv n))) (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_cplc syn_wrex syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0057
  have p0058 :=
    @g_syl221anc (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.objMem y k) (.classMem (.cv z) (syn_ccompl (.cv y))) (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n))) p0053 p0025 p0054 p0056 p0027 p0058_e05_recanon
  have p0059 :=
    @g_unex (.cv y) (syn_csn (.cv z)) p0028 p0008
  have p0060 :=
    @g_pw1eq (.cv a) (syn_cun (.cv y) (syn_csn (.cv z)))
  have p0061 :=
    @g_eleq1d (.classEq (.cv a) (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc M (syn_c1c)) p0060
  have p0062 :=
    @g_pweq (.cv a) (syn_cun (.cv y) (syn_csn (.cv z)))
  have p0063 :=
    @g_eleq1d (.classEq (.cv a) (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cpw (.cv a)) (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n)) p0062
  have p0064 :=
    @g_anbi12d (.classEq (.cv a) (syn_cun (.cv y) (syn_csn (.cv z)))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc M (syn_c1c))) (.classMem (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc M (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv n) (.cv n))) (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n))) p0061 p0063
  have p0065 :=
    @g_spcev (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc M (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv n) (.cv n)))) (syn_wa (.classMem (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc M (syn_c1c))) (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n)))) a (syn_cun (.cv y) (syn_csn (.cv z))) dv_cache_0019 dv_cache_0020 p0059 p0064
  have p0066 :=
    @g_syl2anc (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (.classMem (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc M (syn_c1c))) (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n))) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc M (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv n) (.cv n))))) p0052 p0058 p0065
  have p0067 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)) a dv_cache_0021 dv_cache_0022
  have p0068 :=
    @g_syl3anbrc (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (.classMem (syn_cplc M (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc M (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv n) (.cv n))))) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))) p0039 p0042 p0066 p0067
  have p0069 :=
    @g_jca (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))))) (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))) p0037 p0068
  have p0070 :=
    @g_expr (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))) p0069
  have p0071 :=
    @g_reximdva (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n))) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))) n (syn_cnnc) dv_cache_0023 p0070
  have p0072 :=
    @g_mpd (syn_w3a (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) p0023 p0071
  have p0073 :=
    @g_n_3expa (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) p0072
  have p0074 :=
    @g_expr (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) p0073
  have p0075 :=
    @g_rexlimdva (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))) (syn_wa (.objMem y k) (.objMem y k)) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) k (syn_cnnc) dv_cache_0024 dv_cache_0025 p0074
  have p0076 :=
    @g_mpd (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))) (syn_wrex k (syn_cnnc) (syn_wa (.objMem y k) (.objMem y k))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) p0019 p0075
  have p0077 :=
    @g_syl6bi (syn_wa (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z)))) (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))) (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) p0016 p0076
  have p0078 :=
    @g_n_3adant1 (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z))) (.imp (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))) (.classEq A (syn_cun (.cv y) (syn_csn (.cv z)))) p0077
  have p0079 :=
    @g_com12 (syn_w3a (.classEq A (syn_cun (.cv y) (syn_csn (.cv z)))) (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z)))) (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) p0078
  have p0080 :=
    @g_exlimdvv (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))) (syn_w3a (.classEq A (syn_cun (.cv y) (syn_csn (.cv z)))) (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z)))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) y z dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 p0079
  have p0081 :=
    @g_syl5bi (.classEq (syn_cpw1 A) (syn_cun (.cv b) (syn_csn (.cv x)))) (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_cun (.cv y) (syn_csn (.cv z)))) (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z)))))) (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) p0003 p0080
  have p0082 :=
    @g_rexlimdvva (.classMem M (syn_cnnc)) (.classEq (syn_cpw1 A) (syn_cun (.cv b) (syn_csn (.cv x)))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) b x M (syn_ccompl (.cv b)) dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0004 p0081
  have p0083 :=
    @g_imp (.classMem M (syn_cnnc)) (syn_wrex b M (syn_wrex x (syn_ccompl (.cv b)) (.classEq (syn_cpw1 A) (syn_cun (.cv b) (syn_csn (.cv x)))))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) p0082
  have p0084 :=
    @g_sylan2b (.classMem (syn_cpw1 A) (syn_cplc M (syn_c1c))) (.classMem M (syn_cnnc)) (syn_wrex b M (syn_wrex x (syn_ccompl (.cv b)) (.classEq (syn_cpw1 A) (syn_cun (.cv b) (syn_csn (.cv x)))))) (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))) p0000 p0083
  exact p0084

#print axioms g_sfindbl

end NFChoice.DirectNominalPrf.WPPReplay
