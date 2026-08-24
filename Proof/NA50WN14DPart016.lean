import NA50WN14DPart015

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

theorem nb050_wpp_notmem_0084 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_037 x A B) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb050_compact_fv_empty_0024 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0085 (x : Var) (y : Var) : (nb050_alpha_dummy_038 x y) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb050_compact_fv_empty_0025 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0086 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_035 x A B) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb050_compact_fv_empty_0026 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0087 (x : Var) (y : Var) : (nb050_alpha_dummy_036 x y) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb050_compact_fv_empty_0027 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0088 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_033 x A B) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb050_compact_fv_empty_0028 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0089 (x : Var) (y : Var) : (nb050_alpha_dummy_034 x y) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb050_compact_fv_empty_0029 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
