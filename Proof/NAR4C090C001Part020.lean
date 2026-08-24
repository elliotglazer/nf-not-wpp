import NAR4C090C001Part019

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb090_support_mem_0635 (h : Var) : (nb090_alpha_dummy_427 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0636 (A : Class) : (nb090_alpha_dummy_424 A) ∈ (((Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0637 (h : Var) : (nb090_alpha_dummy_427 h) ∈ (((Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0638 (A : Class) : (nb090_alpha_dummy_582 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0639 (h : Var) : (nb090_alpha_dummy_584 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0640 (A : Class) : (nb090_alpha_dummy_582 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0641 (h : Var) : (nb090_alpha_dummy_584 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0642 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0643 (v : Var) (u : Var) (h : Var) : u ∈ (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0644 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0645 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0646 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0647 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0648 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0649 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0650 (A : Class) : (nb090_alpha_dummy_618 A) ∈ (((Class.cv (nb090_alpha_dummy_618 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0651 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_620 v u h) ∈ (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0652 (A : Class) : (nb090_alpha_dummy_625 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_625 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_625 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_625 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0653 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_627 v u h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_627 v u h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0654 (A : Class) : (nb090_alpha_dummy_625 A) ∈ (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0655 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_627 v u h) ∈ (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0656 (A : Class) : (nb090_alpha_dummy_632 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0657 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_635 v u h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h)) (Class.cv (nb090_alpha_dummy_636 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h)) (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0658 (A : Class) : (nb090_alpha_dummy_632 A) ∈ (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0659 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_635 v u h) ∈ (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0660 (A : Class) : (nb090_alpha_dummy_633 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0661 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_636 v u h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h)) (Class.cv (nb090_alpha_dummy_636 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h)) (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0662 (A : Class) : (nb090_alpha_dummy_633 A) ∈ (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0663 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_636 v u h) ∈ (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0664 (A : Class) : (nb090_alpha_dummy_632 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_632 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_633 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0665 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_635 v u h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_635 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0666 (A : Class) : (nb090_alpha_dummy_632 A) ∈ (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_632 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0667 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_635 v u h) ∈ (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_635 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0668 (A : Class) : (nb090_alpha_dummy_633 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_632 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_633 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0669 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_636 v u h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_635 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0670 (A : Class) : (nb090_alpha_dummy_633 A) ∈ (((Class.cv (nb090_alpha_dummy_633 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0671 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_636 v u h) ∈ (((Class.cv (nb090_alpha_dummy_636 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0672 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0673 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0674 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0675 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0676 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0677 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0678 (A : Class) : (nb090_alpha_dummy_618 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0679 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_620 v u h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0680 (A : Class) : (nb090_alpha_dummy_618 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0681 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_620 v u h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0682 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0683 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (({(nb090_alpha_dummy_653 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_653 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0684 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_653 A) (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_653 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0683 A) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0682 A) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0685 (u : Var) : u ∈ (((syn_c1st)).fv ∪ ((Class.cv u)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0686 (u : Var) : u ∈ (({(nb090_alpha_dummy_654 u)} : Finset Var) ∪ ((syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0687 (u : Var) : u ∈ (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_654 u) (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))) (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0686 u) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0685 u) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0688 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0689 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0690 (u : Var) : u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0691 (u : Var) : u ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0692 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0693 (u : Var) : u ∈ (((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0694 (A : Class) : (nb090_alpha_dummy_662 A) ∈ (((Class.cv (nb090_alpha_dummy_662 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0695 (u : Var) : (nb090_alpha_dummy_664 u) ∈ (((Class.cv (nb090_alpha_dummy_664 u))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0696 (A : Class) : (nb090_alpha_dummy_669 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_669 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_669 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_669 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0697 (u : Var) : (nb090_alpha_dummy_671 u) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_671 u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_671 u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_671 u))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0698 (A : Class) : (nb090_alpha_dummy_669 A) ∈ (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0699 (u : Var) : (nb090_alpha_dummy_671 u) ∈ (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0700 (A : Class) : (nb090_alpha_dummy_676 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0701 (u : Var) : (nb090_alpha_dummy_679 u) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0702 (A : Class) : (nb090_alpha_dummy_676 A) ∈ (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0703 (u : Var) : (nb090_alpha_dummy_679 u) ∈ (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0704 (A : Class) : (nb090_alpha_dummy_677 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0705 (u : Var) : (nb090_alpha_dummy_680 u) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0706 (A : Class) : (nb090_alpha_dummy_677 A) ∈ (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0707 (u : Var) : (nb090_alpha_dummy_680 u) ∈ (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0708 (A : Class) : (nb090_alpha_dummy_676 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_676 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_677 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0709 (u : Var) : (nb090_alpha_dummy_679 u) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_679 u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_680 u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0710 (A : Class) : (nb090_alpha_dummy_676 A) ∈ (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_676 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0711 (u : Var) : (nb090_alpha_dummy_679 u) ∈ (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_679 u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0712 (A : Class) : (nb090_alpha_dummy_677 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_676 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_677 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0713 (u : Var) : (nb090_alpha_dummy_680 u) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_679 u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_680 u)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0714 (A : Class) : (nb090_alpha_dummy_677 A) ∈ (((Class.cv (nb090_alpha_dummy_677 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0715 (u : Var) : (nb090_alpha_dummy_680 u) ∈ (((Class.cv (nb090_alpha_dummy_680 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0716 (A : Class) : (nb090_alpha_dummy_653 A) ∈ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0717 (A : Class) : (nb090_alpha_dummy_653 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0718 (u : Var) : (nb090_alpha_dummy_654 u) ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0719 (u : Var) : (nb090_alpha_dummy_654 u) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0720 (A : Class) : (nb090_alpha_dummy_653 A) ∈ (((Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0721 (u : Var) : (nb090_alpha_dummy_654 u) ∈ (((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0722 (A : Class) : (nb090_alpha_dummy_662 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0723 (u : Var) : (nb090_alpha_dummy_664 u) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0724 (A : Class) : (nb090_alpha_dummy_662 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0725 (u : Var) : (nb090_alpha_dummy_664 u) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0726 (A : Class) : (nb090_alpha_dummy_655 A) ∈ (((Class.cv (nb090_alpha_dummy_655 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0727 (u : Var) : (nb090_alpha_dummy_656 u) ∈ (((Class.cv (nb090_alpha_dummy_656 u))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0728 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0729 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0730 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0731 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0732 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0733 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0734 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_041 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0735 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (({(nb090_alpha_dummy_707 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0736 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A) (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0735 A) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0734 A) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0737 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_043 v u h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0738 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (({(nb090_alpha_dummy_708 v u h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0739 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_708 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0738 v u h) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0737 v u h) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0740 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0741 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0742 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0743 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0744 (A : Class) : (nb090_alpha_dummy_041 A) ∈ (((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0745 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∈ (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0746 (A : Class) : (nb090_alpha_dummy_716 A) ∈ (((Class.cv (nb090_alpha_dummy_716 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0747 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_718 v u h) ∈ (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0748 (A : Class) : (nb090_alpha_dummy_723 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_723 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_723 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_723 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0749 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_725 v u h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_725 v u h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0750 (A : Class) : (nb090_alpha_dummy_723 A) ∈ (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0751 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_725 v u h) ∈ (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0752 (A : Class) : (nb090_alpha_dummy_730 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0753 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_733 v u h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h)) (Class.cv (nb090_alpha_dummy_734 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h)) (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0754 (A : Class) : (nb090_alpha_dummy_730 A) ∈ (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0755 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_733 v u h) ∈ (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0756 (A : Class) : (nb090_alpha_dummy_731 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0757 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_734 v u h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h)) (Class.cv (nb090_alpha_dummy_734 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h)) (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0758 (A : Class) : (nb090_alpha_dummy_731 A) ∈ (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0759 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_734 v u h) ∈ (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
