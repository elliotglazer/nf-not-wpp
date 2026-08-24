import NA50WN14DPart026

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

theorem nb050_focused_notmem_0003 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_000 x A B) ∉ B.fv := by
  change freshVar (({x} : Finset Var) ∪ (A).fv ∪ (B).fv) 0 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb050_wpp_notmem_0114 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_000 x A B) ∉ (B).fv := by
  simp only [(nb050_focused_notmem_0003 x A B), (nb050_compact_fv_empty_0008 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_wpp_notmem_0115 (y : Var) (B : Class) (dv_B_y : y ∉ B.fv) : y ∉ (B).fv := by
  simp only [dv_B_y, (nb050_compact_fv_empty_0009 y), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_focused_notmem_0004 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_001 x A B) ∉ B.fv := by
  change freshVar (({x} : Finset Var) ∪ ({(nb050_alpha_dummy_000 x A B)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B))).fv) 0 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B)).symm ▸ (Finset.mem_union_right _ (((fv_wff_classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B).symm ▸ (Finset.mem_union_right _ (hu))))))))

theorem nb050_wpp_notmem_0116 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_001 x A B) ∉ (B).fv := by
  simp only [(nb050_focused_notmem_0004 x A B), (nb050_compact_fv_empty_0010 x A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb050_focused_notmem_0005 (x : Var) (y : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_002 x y A B) ∉ B.fv := by
  change freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv) 0 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B)).symm ▸ (Finset.mem_union_right _ (((fv_wff_classEq (Class.cv y) B).symm ▸ (Finset.mem_union_right _ (hu))))))))

theorem nb050_wpp_notmem_0117 (x : Var) (y : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_002 x y A B) ∉ (B).fv := by
  simp only [(nb050_focused_notmem_0005 x y A B), (nb050_compact_fv_empty_0011 x y A B), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
