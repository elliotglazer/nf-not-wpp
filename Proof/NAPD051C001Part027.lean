import NAPD051C001Part026

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

theorem nb051_focused_notmem_0006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ C.fv := by
  change freshVar (({x} : Finset Var) ∪ (A).fv ∪ ({y} : Finset Var) ∪ (B).fv ∪ (C).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (hu))

theorem nb051_wpp_notmem_0114 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ (C).fv := by
  simp only [(nb051_focused_notmem_0006 x y A B C), (nb051_compact_fv_empty_0008 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_wpp_notmem_0115 (z : Var) (C : Class) (dv_C_z : z ∉ C.fv) : z ∉ (C).fv := by
  simp only [dv_C_z, (nb051_compact_fv_empty_0009 z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_focused_notmem_0007 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ C.fv := by
  change freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C)).symm ▸ (Finset.mem_union_right _ (((fv_wff_classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C).symm ▸ (Finset.mem_union_right _ (hu))))))))

theorem nb051_wpp_notmem_0116 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ (C).fv := by
  simp only [(nb051_focused_notmem_0007 x y A B C), (nb051_compact_fv_empty_0010 x y A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_focused_notmem_0008 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ C.fv := by
  change freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C)).symm ▸ (Finset.mem_union_right _ (((fv_wff_classEq (Class.cv z) C).symm ▸ (Finset.mem_union_right _ (hu))))))))

theorem nb051_wpp_notmem_0117 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ (C).fv := by
  simp only [(nb051_focused_notmem_0008 x y z A B C), (nb051_compact_fv_empty_0011 x y z A B C), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
