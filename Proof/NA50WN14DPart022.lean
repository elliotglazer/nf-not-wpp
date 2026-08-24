import NA50WN14DPart021

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

theorem nb050_wpp_notmem_0096 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_035 x A B) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0026 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0097 (x : Var) (y : Var) : (nb050_alpha_dummy_036 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0027 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0098 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_004 x A B) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0000 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0099 (x : Var) (y : Var) : (nb050_alpha_dummy_006 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0001 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0100 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_003 x A B) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0002 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0101 (x : Var) (y : Var) : (nb050_alpha_dummy_005 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0003 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0102 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_033 x A B) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0028 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0103 (x : Var) (y : Var) : (nb050_alpha_dummy_034 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0029 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0104 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_007 x A B) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0006 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0105 (x : Var) (y : Var) : (nb050_alpha_dummy_008 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0007 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0106 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_000 x A B) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0008 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0107 (y : Var) : y ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0009 y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0108 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_001 x A B) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0010 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0109 (x : Var) (y : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_002 x y A B) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c, (nb050_compact_fv_empty_0011 x y A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
