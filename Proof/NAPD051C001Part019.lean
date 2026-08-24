import NAPD051C001Part018

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

theorem nb051_wpp_notmem_0090 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_037 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0024 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0091 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_038 x y z) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0025 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0092 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_035 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0026 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0093 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_036 x y z) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0027 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0094 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_033 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0028 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0095 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_034 x y z) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0029 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
