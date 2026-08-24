import NAPD051C001Part013

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

theorem nb051_compact_fv_empty_0024 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_037 x y A B C) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0078 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_037 x y A B C) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb051_compact_fv_empty_0024 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_compact_fv_empty_0025 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_038 x y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0079 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_038 x y z) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb051_compact_fv_empty_0025 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_compact_fv_empty_0026 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_035 x y A B C) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0080 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_035 x y A B C) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb051_compact_fv_empty_0026 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_compact_fv_empty_0027 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_036 x y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0081 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_036 x y z) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb051_compact_fv_empty_0027 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_compact_fv_empty_0028 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_033 x y A B C) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0082 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_033 x y A B C) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb051_compact_fv_empty_0028 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_compact_fv_empty_0029 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_034 x y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb051_wpp_notmem_0083 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_034 x y z) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb051_compact_fv_empty_0029 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
