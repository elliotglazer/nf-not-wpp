import NA50WN14DPart002

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

theorem nb050_support_mem_0001 (x : Var) (y : Var) (A : Class) (B : Class) : x ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0002 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_000 x A B) ∈ (({x} : Finset Var) ∪ ({(nb050_alpha_dummy_000 x A B)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0003 (x : Var) (y : Var) (A : Class) (B : Class) : y ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0004 (x : Var) (A : Class) (B : Class) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0005 (x : Var) (y : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0006 (x : Var) (A : Class) (B : Class) : x ∈ (((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0007 (x : Var) (y : Var) : x ∈ (((Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0008 (x : Var) (A : Class) (B : Class) : x ∈ (((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))))))).fv ∪ ((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B)) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0009 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0010 (x : Var) (A : Class) (B : Class) : x ∈ (({x} : Finset Var) ∪ (A).fv ∪ (B).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0011 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_004 x A B) ∈ (((Class.cv (nb050_alpha_dummy_004 x A B))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0012 (x : Var) (y : Var) : (nb050_alpha_dummy_006 x y) ∈ (((Class.cv (nb050_alpha_dummy_006 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0013 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_011 x A B) ∈ (((Wff.classMem (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb050_alpha_dummy_011 x A B)) (syn_c1c))).fv ∪ ((Class.cv (nb050_alpha_dummy_011 x A B))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0014 (x : Var) (y : Var) : (nb050_alpha_dummy_013 x y) ∈ (((Wff.classMem (Class.cv (nb050_alpha_dummy_013 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb050_alpha_dummy_013 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb050_alpha_dummy_013 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0015 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_011 x A B) ∈ (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0016 (x : Var) (y : Var) : (nb050_alpha_dummy_013 x y) ∈ (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0017 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_018 x A B) ∈ (((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B)) (Class.cv (nb050_alpha_dummy_019 x A B)))).fv ∪ ((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B)) (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0018 (x : Var) (y : Var) : (nb050_alpha_dummy_021 x y) ∈ (((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y)) (Class.cv (nb050_alpha_dummy_022 x y)))).fv ∪ ((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y)) (Class.cv (nb050_alpha_dummy_022 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0019 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_018 x A B) ∈ (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪ ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0020 (x : Var) (y : Var) : (nb050_alpha_dummy_021 x y) ∈ (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪ ((Class.cv (nb050_alpha_dummy_022 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0021 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_019 x A B) ∈ (((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B)) (Class.cv (nb050_alpha_dummy_019 x A B)))).fv ∪ ((syn_cnin (Class.cv (nb050_alpha_dummy_018 x A B)) (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0022 (x : Var) (y : Var) : (nb050_alpha_dummy_022 x y) ∈ (((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y)) (Class.cv (nb050_alpha_dummy_022 x y)))).fv ∪ ((syn_cnin (Class.cv (nb050_alpha_dummy_021 x y)) (Class.cv (nb050_alpha_dummy_022 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0023 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_019 x A B) ∈ (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪ ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0024 (x : Var) (y : Var) : (nb050_alpha_dummy_022 x y) ∈ (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪ ((Class.cv (nb050_alpha_dummy_022 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0025 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_018 x A B) ∈ (((syn_ccompl (Class.cv (nb050_alpha_dummy_018 x A B)))).fv ∪ ((syn_ccompl (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0026 (x : Var) (y : Var) : (nb050_alpha_dummy_021 x y) ∈ (((syn_ccompl (Class.cv (nb050_alpha_dummy_021 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb050_alpha_dummy_022 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0027 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_018 x A B) ∈ (((Class.cv (nb050_alpha_dummy_018 x A B))).fv ∪ ((Class.cv (nb050_alpha_dummy_018 x A B))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0028 (x : Var) (y : Var) : (nb050_alpha_dummy_021 x y) ∈ (((Class.cv (nb050_alpha_dummy_021 x y))).fv ∪ ((Class.cv (nb050_alpha_dummy_021 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0029 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_019 x A B) ∈ (((syn_ccompl (Class.cv (nb050_alpha_dummy_018 x A B)))).fv ∪ ((syn_ccompl (Class.cv (nb050_alpha_dummy_019 x A B)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0030 (x : Var) (y : Var) : (nb050_alpha_dummy_022 x y) ∈ (((syn_ccompl (Class.cv (nb050_alpha_dummy_021 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb050_alpha_dummy_022 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0031 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_019 x A B) ∈ (((Class.cv (nb050_alpha_dummy_019 x A B))).fv ∪ ((Class.cv (nb050_alpha_dummy_019 x A B))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0032 (x : Var) (y : Var) : (nb050_alpha_dummy_022 x y) ∈ (((Class.cv (nb050_alpha_dummy_022 x y))).fv ∪ ((Class.cv (nb050_alpha_dummy_022 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0033 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_000 x A B) ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0034 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_000 x A B) ∈ (((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))))))).fv ∪ ((syn_ccompl (Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B)) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0033 x A B) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0033 x A B) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0035 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0036 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv x) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0035 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0035 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0037 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_000 x A B) ∈ (((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B)) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_003 x A B) (syn_wrex (nb050_alpha_dummy_004 x A B) (Class.cv (nb050_alpha_dummy_000 x A B)) (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0033 x A B) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0033 x A B) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0038 (x : Var) (y : Var) : y ∈ (((Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb050_alpha_dummy_005 x y) (syn_wrex (nb050_alpha_dummy_006 x y) (Class.cv y) (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y)) (syn_cun (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0035 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0035 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb050_support_mem_0039 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_004 x A B) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0040 (x : Var) (y : Var) : (nb050_alpha_dummy_006 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0041 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_004 x A B) ∈ (((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv ∪ ((syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_support_mem_0042 (x : Var) (y : Var) : (nb050_alpha_dummy_006 x y) ∈ (((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv ∪ ((syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb050_compact_fv_empty_0000 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_004 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0000 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_004 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 1)))

theorem nb050_compact_fv_empty_0001 (x : Var) (y : Var) : (nb050_alpha_dummy_006 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0001 (x : Var) (y : Var) : (nb050_alpha_dummy_006 x y) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 1)))

theorem nb050_compact_fv_empty_0002 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_003 x A B) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0002 (x : Var) (A : Class) (B : Class) : (nb050_alpha_dummy_003 x A B) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0004 x A B) 0)))

theorem nb050_compact_fv_empty_0003 (x : Var) (y : Var) : (nb050_alpha_dummy_005 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb050_wpp_notmem_0003 (x : Var) (y : Var) : (nb050_alpha_dummy_005 x y) ∉ ((Class.cv x)).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0005 x y) 0)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
