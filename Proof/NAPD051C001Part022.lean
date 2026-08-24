import NAPD051C001Part021

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

theorem nb051_wpp_notmem_0096 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_035 x y A B C) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0026 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0097 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_036 x y z) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0027 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0098 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_004 x y A B C) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0000 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0099 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_006 x y z) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0001 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0100 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_003 x y A B C) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0002 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0101 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_005 x y z) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0003 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0102 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_033 x y A B C) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0028 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0103 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_034 x y z) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0029 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0104 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_007 x y A B C) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0006 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0105 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_008 x y z) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0007 x y z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0106 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0008 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0107 (z : Var) : z ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0009 z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0108 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0010 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0109 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb051_compact_fv_empty_0011 x y z A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
