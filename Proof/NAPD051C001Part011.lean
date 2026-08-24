import NAPD051C001Part010

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

theorem nb051_wpp_notmem_0060 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_015 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0018 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0061 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_016 x y z) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0019 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0062 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_011 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0020 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0063 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_013 x y z) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0021 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0064 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_012 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0022 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0065 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_014 x y z) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0023 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0066 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_004 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0000 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0067 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_006 x y z) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0001 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0068 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_003 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0002 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0069 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_005 x y z) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0003 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0070 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_009 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0004 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0071 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_010 x y z) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0005 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0072 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_007 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0006 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0073 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_008 x y z) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0007 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0074 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0008 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0075 (z : Var) : z ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0009 z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0076 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0010 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0077 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ ((syn_cnnc)).fv := by
  simp only [fv_syn_cnnc, (nb051_compact_fv_empty_0011 x y z A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
