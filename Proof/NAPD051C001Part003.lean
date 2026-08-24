import NAPD051C001Part002

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

theorem nb051_support_mem_0001 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : x ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0002 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : y ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0003 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : y ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0005 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : z ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : x ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0007 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : y ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0008 (x : Var) (y : Var) (z : Var) : x ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0009 (x : Var) (y : Var) (z : Var) : y ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0010 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : x ∈ (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0011 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : y ∈ (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0012 (x : Var) (y : Var) (z : Var) : x ∈ (((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0013 (x : Var) (y : Var) (z : Var) : y ∈ (((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0014 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : x ∈ (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0006 x y A B C) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0015 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : y ∈ (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0007 x y A B C) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0016 (x : Var) (y : Var) (z : Var) : x ∈ (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0008 x y z) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0017 (x : Var) (y : Var) (z : Var) : y ∈ (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0009 x y z) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0018 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : x ∈ (({x} : Finset Var) ∪ (A).fv ∪ ({y} : Finset Var) ∪ (B).fv ∪ (C).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0019 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : y ∈ (({x} : Finset Var) ∪ (A).fv ∪ ({y} : Finset Var) ∪ (B).fv ∪ (C).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0020 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_004 x y A B C) ∈ (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0021 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_006 x y z) ∈ (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0022 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_011 x y A B C) ∈ (((Wff.classMem (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_c1c))).fv ∪ ((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0023 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_013 x y z) ∈ (((Wff.classMem (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_c1c))).fv ∪ ((Class.cv (nb051_alpha_dummy_013 x y z))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0024 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_011 x y A B C) ∈ (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0025 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_013 x y z) ∈ (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0026 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_018 x y A B C) ∈ (((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C)) (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv ∪ ((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C)) (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0027 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_021 x y z) ∈ (((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z)) (Class.cv (nb051_alpha_dummy_022 x y z)))).fv ∪ ((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z)) (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0028 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_018 x y A B C) ∈ (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0029 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_021 x y z) ∈ (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0030 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_019 x y A B C) ∈ (((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C)) (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv ∪ ((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C)) (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0031 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_022 x y z) ∈ (((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z)) (Class.cv (nb051_alpha_dummy_022 x y z)))).fv ∪ ((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z)) (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0032 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_019 x y A B C) ∈ (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0033 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_022 x y z) ∈ (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0034 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_018 x y A B C) ∈ (((syn_ccompl (Class.cv (nb051_alpha_dummy_018 x y A B C)))).fv ∪ ((syn_ccompl (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0035 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_021 x y z) ∈ (((syn_ccompl (Class.cv (nb051_alpha_dummy_021 x y z)))).fv ∪ ((syn_ccompl (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0036 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_018 x y A B C) ∈ (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0037 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_021 x y z) ∈ (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_021 x y z))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0038 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_019 x y A B C) ∈ (((syn_ccompl (Class.cv (nb051_alpha_dummy_018 x y A B C)))).fv ∪ ((syn_ccompl (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0039 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_022 x y z) ∈ (((syn_ccompl (Class.cv (nb051_alpha_dummy_021 x y z)))).fv ∪ ((syn_ccompl (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0040 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_019 x y A B C) ∈ (((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0041 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_022 x y z) ∈ (((Class.cv (nb051_alpha_dummy_022 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0042 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0043 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∈ (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0044 (x : Var) (y : Var) (z : Var) : z ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0045 (x : Var) (y : Var) (z : Var) : z ∈ (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0046 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∈ (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0047 (x : Var) (y : Var) (z : Var) : z ∈ (((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb051_support_mem_0048 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_004 x y A B C) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0049 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_006 x y z) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb051_support_mem_0050 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_004 x y A B C) ∈ (((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv ∪ ((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
