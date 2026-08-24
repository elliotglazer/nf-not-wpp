import NAPD051C001Part003

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

theorem nb051_support_mem_0051 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_006 x y z) ∈ (((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv ∪ ((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_compact_fv_empty_0000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_004 x y A B C) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_004 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_004, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 1))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 1))))

theorem nb051_compact_fv_empty_0001 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_006 x y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0001 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_006 x y z) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_006, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 1))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 1))))

theorem nb051_compact_fv_empty_0002 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_003 x y A B C) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0002 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_003 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_003, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 0))))

theorem nb051_compact_fv_empty_0003 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_005 x y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0003 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_005 x y z) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_005, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 0))))

theorem nb051_compact_fv_empty_0004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_009 x y A B C) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_009 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_009, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0010 x y A B C) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0011 x y A B C) 0))))

theorem nb051_compact_fv_empty_0005 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_010 x y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0005 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_010 x y z) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_010, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0012 x y z) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0013 x y z) 0))))

theorem nb051_compact_fv_empty_0006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_007 x y A B C) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_007 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_007, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0014 x y A B C) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0015 x y A B C) 0))))

theorem nb051_compact_fv_empty_0007 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_008 x y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0007 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_008 x y z) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_008, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0016 x y z) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0017 x y z) 0))))

theorem nb051_compact_fv_empty_0008 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0008 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_000, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0018 x y A B C) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0019 x y A B C) 0))))

theorem nb051_compact_fv_empty_0009 (z : Var) : z ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0009 (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) : z ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simp only [fv_syn_cop, Finset.mem_union, fv_class_cv, (Ne.symm dv_x_z), Finset.mem_singleton, (Ne.symm dv_y_z), (nb051_compact_fv_empty_0009 z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_compact_fv_empty_0010 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0010 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_001, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0000 x y A B C) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0002 x y A B C) 0))))

theorem nb051_compact_fv_empty_0011 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0011 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  simpa only [nb051_alpha_dummy_002, fv_syn_cop, Finset.mem_union, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0001 x y z A B C) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0003 x y z A B C) 0))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
