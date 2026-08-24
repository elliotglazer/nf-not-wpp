import NA50WN14DPart005

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

theorem nb050_compact_fv_empty_0012 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_019 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0012 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_019 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0012 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0013 (x : Var) (y : Var) : (nb050_alpha_dummy_022 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0013 (x : Var) (y : Var) : (nb050_alpha_dummy_022 x y) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0013 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0014 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_018 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0014 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_018 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0014 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0015 (x : Var) (y : Var) : (nb050_alpha_dummy_021 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0015 (x : Var) (y : Var) : (nb050_alpha_dummy_021 x y) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0015 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0016 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_017 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0016 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_017 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0016 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0017 (x : Var) (y : Var) : (nb050_alpha_dummy_020 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0017 (x : Var) (y : Var) : (nb050_alpha_dummy_020 x y) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0017 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0018 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_015 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0018 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_015 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0018 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0019 (x : Var) (y : Var) : (nb050_alpha_dummy_016 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0019 (x : Var) (y : Var) : (nb050_alpha_dummy_016 x y) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0019 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0020 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_011 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0020 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_011 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0020 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0021 (x : Var) (y : Var) : (nb050_alpha_dummy_013 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0021 (x : Var) (y : Var) : (nb050_alpha_dummy_013 x y) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0021 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0022 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_012 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0022 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_012 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0022 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_compact_fv_empty_0023 (x : Var) (y : Var) : (nb050_alpha_dummy_014 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0023 (x : Var) (y : Var) : (nb050_alpha_dummy_014 x y) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0023 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0024 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_004 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0000 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0025 (x : Var) (y : Var) : (nb050_alpha_dummy_006 x y) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0001 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0026 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_003 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0002 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0027 (x : Var) (y : Var) : (nb050_alpha_dummy_005 x y) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0003 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0028 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_009 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0004 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0029 (x : Var) (y : Var) : (nb050_alpha_dummy_010 x y) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0005 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0030 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_007 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0006 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0031 (x : Var) (y : Var) : (nb050_alpha_dummy_008 x y) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0007 x y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0032 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_000 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0008 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0033 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0009 y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0034 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_001 x A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0010 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0035 (x : Var) (y : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_002 x y A B) ∉ ((syn_c1c)).fv := by
  simp only [fv_syn_c1c, (nb050_compact_fv_empty_0011 x y A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
