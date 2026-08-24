import NAPD051C001Part024

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

theorem nb051_focused_notmem_0000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ A.fv := by
  change freshVar (({x} : Finset Var) ∪ (A).fv ∪ ({y} : Finset Var) ∪ (B).fv ∪ (C).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))))

theorem nb051_focused_notmem_0001 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ B.fv := by
  change freshVar (({x} : Finset Var) ∪ (A).fv ∪ ({y} : Finset Var) ∪ (B).fv ∪ (C).fv) 0 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb051_wpp_notmem_0110 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv := by
  simpa only [nb051_alpha_dummy_000, fv_syn_wa, Finset.mem_union, fv_wff_classMem, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0018 x y A B C) 0))) (nb051_focused_notmem_0000 x y A B C)) (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0019 x y A B C) 0))) (nb051_focused_notmem_0001 x y A B C)))

theorem nb051_wpp_notmem_0111 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) : z ∉ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv := by
  simp only [fv_syn_wa, Finset.mem_union, fv_wff_classMem, fv_class_cv, (Ne.symm dv_x_z), Finset.mem_singleton, dv_A_z, (Ne.symm dv_y_z), dv_B_z, (nb051_compact_fv_empty_0009 z), false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true]

theorem nb051_focused_notmem_0002 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ A.fv := by
  change freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C)).symm ▸ (Finset.mem_union_left _ (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv x) A).symm ▸ (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_focused_notmem_0003 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ B.fv := by
  change freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) 0 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C)).symm ▸ (Finset.mem_union_left _ (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)).symm ▸ (Finset.mem_union_right _ (((fv_wff_classMem (Class.cv y) B).symm ▸ (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_wpp_notmem_0112 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv := by
  simpa only [nb051_alpha_dummy_001, fv_syn_wa, Finset.mem_union, fv_wff_classMem, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0000 x y A B C) 0))) (nb051_focused_notmem_0002 x y A B C)) (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0002 x y A B C) 0))) (nb051_focused_notmem_0003 x y A B C)))

theorem nb051_focused_notmem_0004 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ A.fv := by
  change freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C)).symm ▸ (Finset.mem_union_left _ (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv x) A).symm ▸ (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_focused_notmem_0005 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ B.fv := by
  change freshVar (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C))).fv) 0 ∉ B.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C)).symm ▸ (Finset.mem_union_left _ (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)).symm ▸ (Finset.mem_union_right _ (((fv_wff_classMem (Class.cv y) B).symm ▸ (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_wpp_notmem_0113 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv := by
  simpa only [nb051_alpha_dummy_002, fv_syn_wa, Finset.mem_union, fv_wff_classMem, fv_class_cv, Finset.mem_singleton, not_or] using (And.intro (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0001 x y z A B C) 0))) (nb051_focused_notmem_0004 x y z A B C)) (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0003 x y z A B C) 0))) (nb051_focused_notmem_0005 x y z A B C)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
