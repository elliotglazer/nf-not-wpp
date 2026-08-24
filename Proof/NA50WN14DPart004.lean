import NA50WN14DPart003

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

theorem nb050_compact_fv_empty_0004 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_009 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0004 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_009 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0006 x A B) 0)))

theorem nb050_compact_fv_empty_0005 (x : Var) (y : Var) : (nb050_alpha_dummy_010 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0005 (x : Var) (y : Var) : (nb050_alpha_dummy_010 x y) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0007 x y) 0)))

theorem nb050_compact_fv_empty_0006 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_007 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0006 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_007 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0008 x A B) 0)))

theorem nb050_compact_fv_empty_0007 (x : Var) (y : Var) : (nb050_alpha_dummy_008 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0007 (x : Var) (y : Var) : (nb050_alpha_dummy_008 x y) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0009 x y) 0)))

theorem nb050_compact_fv_empty_0008 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_000 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0008 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_000 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0010 x A B) 0)))

theorem nb050_compact_fv_empty_0009 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0009 (x : Var) (y : Var) (dv_x_y : x ≠ y) : y ∉ ((Class.cv x)).fv := by
  simp only [fv_class_cv, (Ne.symm dv_x_y), Finset.mem_singleton, (nb050_compact_fv_empty_0009 y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0010 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_001 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0010 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_001 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0000 x A B) 0)))

theorem nb050_compact_fv_empty_0011 (x : Var) (y : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_002 x y A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0011 (x : Var) (y : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_002 x y A B) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0001 x y A B) 0)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
