import NAPD051C001Part007

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

theorem nb051_wpp_notmem_0036 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_019 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0012 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0037 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_022 x y z) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0013 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0038 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_018 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0014 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0039 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_021 x y z) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0015 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0040 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_017 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0016 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0041 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_020 x y z) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0017 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0042 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_015 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0018 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0043 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_016 x y z) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0019 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0044 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_011 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0020 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0045 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_013 x y z) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0021 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0046 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_012 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0022 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0047 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_014 x y z) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0023 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0048 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_004 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0000 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0049 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_006 x y z) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0001 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0050 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_003 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0002 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0051 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_005 x y z) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0003 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0052 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_009 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0004 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0053 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_010 x y z) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0005 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0054 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_007 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0006 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0055 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_008 x y z) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0007 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0056 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0008 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0057 (z : Var) : z ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0009 z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0058 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0010 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0059 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ ((syn_c0)).fv := by
  simp only [fv_syn_c0, (nb051_compact_fv_empty_0011 x y z A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
