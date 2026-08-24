import NAR4C090C001Part020

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

theorem nb090_support_mem_0760 (A : Class) : (nb090_alpha_dummy_730 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_730 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_731 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0761 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_733 v u h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_733 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0762 (A : Class) : (nb090_alpha_dummy_730 A) ∈ (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_730 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0763 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_733 v u h) ∈ (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_733 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0764 (A : Class) : (nb090_alpha_dummy_731 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_730 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_731 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0765 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_734 v u h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_733 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0766 (A : Class) : (nb090_alpha_dummy_731 A) ∈ (((Class.cv (nb090_alpha_dummy_731 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0767 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_734 v u h) ∈ (((Class.cv (nb090_alpha_dummy_734 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0768 (A : Class) : (nb090_alpha_dummy_707 A) ∈ (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0769 (A : Class) : (nb090_alpha_dummy_707 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0770 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_708 v u h) ∈ (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0771 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_708 v u h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0772 (A : Class) : (nb090_alpha_dummy_707 A) ∈ (((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0773 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_708 v u h) ∈ (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0774 (A : Class) : (nb090_alpha_dummy_716 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0775 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_718 v u h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0776 (A : Class) : (nb090_alpha_dummy_716 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0777 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_718 v u h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0778 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0779 (v : Var) (u : Var) (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0780 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cfv]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0781 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0782 (v : Var) (u : Var) (h : Var) : h ∈ (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cfv]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0783 (v : Var) (u : Var) (h : Var) : h ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0784 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0785 (v : Var) (u : Var) (h : Var) : h ∈ (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0786 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_041 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0787 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (({(nb090_alpha_dummy_707 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0788 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A) (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0787 A) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0786 A) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0789 (v : Var) (u : Var) (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_043 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0790 (v : Var) (u : Var) (h : Var) : h ∈ (({(nb090_alpha_dummy_708 v u h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0791 (v : Var) (u : Var) (h : Var) : h ∈ (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_708 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0790 v u h) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0789 v u h) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0792 (A : Class) : (nb090_alpha_dummy_709 A) ∈ (((Class.cv (nb090_alpha_dummy_709 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0793 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_710 v u h) ∈ (((Class.cv (nb090_alpha_dummy_710 v u h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0794 (A : Class) : (nb090_alpha_dummy_700 A) ∈ (((Class.cv (nb090_alpha_dummy_700 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0795 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_702 v u h) ∈ (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0796 (A : Class) : (nb090_alpha_dummy_753 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_753 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_753 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_753 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0797 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_755 v u h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_755 v u h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0798 (A : Class) : (nb090_alpha_dummy_753 A) ∈ (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0799 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_755 v u h) ∈ (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0800 (A : Class) : (nb090_alpha_dummy_760 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0801 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_763 v u h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h)) (Class.cv (nb090_alpha_dummy_764 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h)) (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0802 (A : Class) : (nb090_alpha_dummy_760 A) ∈ (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0803 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_763 v u h) ∈ (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0804 (A : Class) : (nb090_alpha_dummy_761 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0805 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_764 v u h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h)) (Class.cv (nb090_alpha_dummy_764 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h)) (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0806 (A : Class) : (nb090_alpha_dummy_761 A) ∈ (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0807 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_764 v u h) ∈ (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0808 (A : Class) : (nb090_alpha_dummy_760 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_760 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_761 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0809 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_763 v u h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_763 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0810 (A : Class) : (nb090_alpha_dummy_760 A) ∈ (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_760 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0811 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_763 v u h) ∈ (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_763 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0812 (A : Class) : (nb090_alpha_dummy_761 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_760 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_761 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0813 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_764 v u h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_763 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0814 (A : Class) : (nb090_alpha_dummy_761 A) ∈ (((Class.cv (nb090_alpha_dummy_761 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0815 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_764 v u h) ∈ (((Class.cv (nb090_alpha_dummy_764 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0816 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0817 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0818 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0819 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0820 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0821 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0822 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0823 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (({(nb090_alpha_dummy_777 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0824 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0823 A) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0822 A) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0825 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0826 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (({(nb090_alpha_dummy_778 v u h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0827 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0826 v u h) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0825 v u h) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0828 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0829 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0830 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0831 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0832 (A : Class) : (nb090_alpha_dummy_042 A) ∈ (((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0833 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∈ (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0834 (A : Class) : (nb090_alpha_dummy_786 A) ∈ (((Class.cv (nb090_alpha_dummy_786 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0835 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_788 v u h) ∈ (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0836 (A : Class) : (nb090_alpha_dummy_793 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_793 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_793 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_793 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0837 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_795 v u h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_795 v u h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0838 (A : Class) : (nb090_alpha_dummy_793 A) ∈ (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0839 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_795 v u h) ∈ (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0840 (A : Class) : (nb090_alpha_dummy_800 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0841 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_803 v u h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h)) (Class.cv (nb090_alpha_dummy_804 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h)) (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0842 (A : Class) : (nb090_alpha_dummy_800 A) ∈ (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0843 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_803 v u h) ∈ (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0844 (A : Class) : (nb090_alpha_dummy_801 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0845 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_804 v u h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h)) (Class.cv (nb090_alpha_dummy_804 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h)) (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0846 (A : Class) : (nb090_alpha_dummy_801 A) ∈ (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0847 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_804 v u h) ∈ (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0848 (A : Class) : (nb090_alpha_dummy_800 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_800 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_801 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0849 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_803 v u h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_803 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0850 (A : Class) : (nb090_alpha_dummy_800 A) ∈ (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_800 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0851 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_803 v u h) ∈ (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_803 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0852 (A : Class) : (nb090_alpha_dummy_801 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_800 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_801 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0853 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_804 v u h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_803 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0854 (A : Class) : (nb090_alpha_dummy_801 A) ∈ (((Class.cv (nb090_alpha_dummy_801 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0855 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_804 v u h) ∈ (((Class.cv (nb090_alpha_dummy_804 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0856 (A : Class) : (nb090_alpha_dummy_777 A) ∈ (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0857 (A : Class) : (nb090_alpha_dummy_777 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0858 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_778 v u h) ∈ (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0859 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_778 v u h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0860 (A : Class) : (nb090_alpha_dummy_777 A) ∈ (((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0861 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_778 v u h) ∈ (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0862 (A : Class) : (nb090_alpha_dummy_786 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0863 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_788 v u h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0864 (A : Class) : (nb090_alpha_dummy_786 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0865 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_788 v u h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0866 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0867 (v : Var) (u : Var) (h : Var) : h ∈ (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0868 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0869 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (({(nb090_alpha_dummy_777 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0870 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0869 A) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0868 A) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0871 (v : Var) (u : Var) (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0872 (v : Var) (u : Var) (h : Var) : h ∈ (({(nb090_alpha_dummy_778 v u h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0873 (v : Var) (u : Var) (h : Var) : h ∈ (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0872 v u h) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0871 v u h) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0874 (A : Class) : (nb090_alpha_dummy_779 A) ∈ (((Class.cv (nb090_alpha_dummy_779 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0875 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_780 v u h) ∈ (((Class.cv (nb090_alpha_dummy_780 v u h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0876 (A : Class) : (nb090_alpha_dummy_700 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0877 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_702 v u h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0878 (A : Class) : (nb090_alpha_dummy_700 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0879 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_702 v u h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0880 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0881 (v : Var) (u : Var) (h : Var) : v ∈ (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0882 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0883 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (({(nb090_alpha_dummy_827 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0884 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0883 A) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0882 A) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
