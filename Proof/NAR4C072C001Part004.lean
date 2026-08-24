import NAR4C072C001Part003

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

theorem nb072_support_mem_0029 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0030 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0031 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0032 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_002 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0033 (x : Var) (y : Var) : y ∈ (((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_004 x y) (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0030 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0034 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_003 A B R S_cls H) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0035 (x : Var) (y : Var) : (nb072_alpha_dummy_005 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0036 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_003 A B R S_cls H) ∈ (((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0037 (x : Var) (y : Var) : (nb072_alpha_dummy_005 x y) ∈ (((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0038 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪ ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0039 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0038 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0038 A B R S_cls H) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0040 (x : Var) (y : Var) (H : Class) : x ∈ (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0041 (x : Var) (y : Var) (H : Class) : x ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0042 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0038 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0038 A B R S_cls H) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0043 (x : Var) (y : Var) (H : Class) : x ∈ (((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0040 x y H) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0044 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0045 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (({(nb072_alpha_dummy_046 A B R S_cls H)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0046 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0045 A B R S_cls H) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0044 A B R S_cls H) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0047 (x : Var) (H : Class) : x ∈ ((H).fv ∪ ((Class.cv x)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0048 (x : Var) (H : Class) : x ∈ (({(nb072_alpha_dummy_047 x H)} : Finset Var) ∪ ((syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0049 (x : Var) (H : Class) : x ∈ (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq (Class.cab (nb072_alpha_dummy_047 x H) (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))) (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0048 x H) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0047 x H) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0050 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0051 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0052 (x : Var) (H : Class) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0053 (x : Var) (H : Class) : x ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0054 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∈ (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0055 (x : Var) (H : Class) : x ∈ (((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0052 x H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0056 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_055 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0057 (x : Var) (H : Class) : (nb072_alpha_dummy_057 x H) ∈ (((Class.cv (nb072_alpha_dummy_057 x H))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0058 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_062 A B R S_cls H) ∈ (((Wff.classMem (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_062 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0059 (x : Var) (H : Class) : (nb072_alpha_dummy_064 x H) ∈ (((Wff.classMem (Class.cv (nb072_alpha_dummy_064 x H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_064 x H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_064 x H))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0060 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_062 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0061 (x : Var) (H : Class) : (nb072_alpha_dummy_064 x H) ∈ (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0062 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_069 A B R S_cls H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0063 (x : Var) (H : Class) : (nb072_alpha_dummy_072 x H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H)) (Class.cv (nb072_alpha_dummy_073 x H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H)) (Class.cv (nb072_alpha_dummy_073 x H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0064 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_069 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0065 (x : Var) (H : Class) : (nb072_alpha_dummy_072 x H) ∈ (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_073 x H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0066 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_070 A B R S_cls H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0067 (x : Var) (H : Class) : (nb072_alpha_dummy_073 x H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H)) (Class.cv (nb072_alpha_dummy_073 x H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_072 x H)) (Class.cv (nb072_alpha_dummy_073 x H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0068 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_070 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0069 (x : Var) (H : Class) : (nb072_alpha_dummy_073 x H) ∈ (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_073 x H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0070 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_069 A B R S_cls H) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0071 (x : Var) (H : Class) : (nb072_alpha_dummy_072 x H) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_072 x H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_073 x H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0072 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_069 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_069 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0073 (x : Var) (H : Class) : (nb072_alpha_dummy_072 x H) ∈ (((Class.cv (nb072_alpha_dummy_072 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_072 x H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0074 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_070 A B R S_cls H) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_069 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_070 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0075 (x : Var) (H : Class) : (nb072_alpha_dummy_073 x H) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_072 x H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_073 x H)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0076 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_070 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_070 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0077 (x : Var) (H : Class) : (nb072_alpha_dummy_073 x H) ∈ (((Class.cv (nb072_alpha_dummy_073 x H))).fv ∪ ((Class.cv (nb072_alpha_dummy_073 x H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0078 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_046 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0079 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_046 A B R S_cls H) ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0080 (x : Var) (H : Class) : (nb072_alpha_dummy_047 x H) ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0081 (x : Var) (H : Class) : (nb072_alpha_dummy_047 x H) ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0082 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_046 A B R S_cls H) ∈ (((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_054 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H) (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0078 A B R S_cls H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0083 (x : Var) (H : Class) : (nb072_alpha_dummy_047 x H) ∈ (((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_056 x H) (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv (nb072_alpha_dummy_047 x H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0080 x H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0084 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_055 A B R S_cls H) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0085 (x : Var) (H : Class) : (nb072_alpha_dummy_057 x H) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0086 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_055 A B R S_cls H) ∈ (((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0087 (x : Var) (H : Class) : (nb072_alpha_dummy_057 x H) ∈ (((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv ∪ ((syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0088 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_048 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_048 A B R S_cls H))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0089 (x : Var) (H : Class) : (nb072_alpha_dummy_049 x H) ∈ (((Class.cv (nb072_alpha_dummy_049 x H))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0090 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_039 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_039 A B R S_cls H))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0091 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_041 x y H) ∈ (((Class.cv (nb072_alpha_dummy_041 x y H))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0092 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_092 A B R S_cls H) ∈ (((Wff.classMem (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_092 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0093 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_094 x y H) ∈ (((Wff.classMem (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_094 x y H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_094 x y H))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0094 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_092 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0095 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_094 x y H) ∈ (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0096 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_099 A B R S_cls H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0097 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_102 x y H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H)) (Class.cv (nb072_alpha_dummy_103 x y H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H)) (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0098 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_099 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0099 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_102 x y H) ∈ (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0100 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_100 A B R S_cls H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0101 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_103 x y H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H)) (Class.cv (nb072_alpha_dummy_103 x y H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_102 x y H)) (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0102 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_100 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0103 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_103 x y H) ∈ (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0104 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_099 A B R S_cls H) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0105 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_102 x y H) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_102 x y H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0106 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_099 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_099 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0107 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_102 x y H) ∈ (((Class.cv (nb072_alpha_dummy_102 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_102 x y H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0108 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_100 A B R S_cls H) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_099 A B R S_cls H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_100 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0109 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_103 x y H) ∈ (((syn_ccompl (Class.cv (nb072_alpha_dummy_102 x y H)))).fv ∪ ((syn_ccompl (Class.cv (nb072_alpha_dummy_103 x y H)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0110 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_100 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_100 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0111 (x : Var) (y : Var) (H : Class) : (nb072_alpha_dummy_103 x y H) ∈ (((Class.cv (nb072_alpha_dummy_103 x y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_103 x y H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0112 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪ ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0113 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0112 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0112 A B R S_cls H) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0114 (x : Var) (y : Var) (H : Class) : y ∈ (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0115 (x : Var) (y : Var) (H : Class) : y ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0116 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H) (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))) (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0112 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0112 A B R S_cls H) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0117 (x : Var) (y : Var) (H : Class) : y ∈ (((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H) (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y)) (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0114 x y H) 1))
    ·
      rw [fv_syn_cfv]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0118 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0119 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (({(nb072_alpha_dummy_116 A B R S_cls H)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0120 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq (Class.cab (nb072_alpha_dummy_116 A B R S_cls H) (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))) (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0119 A B R S_cls H) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0118 A B R S_cls H) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0121 (y : Var) (H : Class) : y ∈ ((H).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0122 (y : Var) (H : Class) : y ∈ (({(nb072_alpha_dummy_117 y H)} : Finset Var) ∪ ((syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0123 (y : Var) (H : Class) : y ∈ (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H) (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))) (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0122 y H) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0121 y H) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0124 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0125 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0126 (y : Var) (H : Class) : y ∈ (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0127 (y : Var) (H : Class) : y ∈ (((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))))))).fv ∪ ((syn_ccompl (Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv (nb072_alpha_dummy_117 y H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0128 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∈ (((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_124 A B R S_cls H) (syn_wrex (nb072_alpha_dummy_125 A B R S_cls H) (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) (Wff.classEq (Class.cv (nb072_alpha_dummy_124 A B R S_cls H)) (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0124 A B R S_cls H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0129 (y : Var) (H : Class) : y ∈ (((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_126 y H) (syn_wrex (nb072_alpha_dummy_127 y H) (Class.cv y) (Wff.classEq (Class.cv (nb072_alpha_dummy_126 y H)) (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb072_support_mem_0126 y H) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb072_support_mem_0130 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_125 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0131 (y : Var) (H : Class) : (nb072_alpha_dummy_127 y H) ∈ (((Class.cv (nb072_alpha_dummy_127 y H))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0132 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_132 A B R S_cls H) ∈ (((Wff.classMem (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_132 A B R S_cls H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0133 (y : Var) (H : Class) : (nb072_alpha_dummy_134 y H) ∈ (((Wff.classMem (Class.cv (nb072_alpha_dummy_134 y H)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb072_alpha_dummy_134 y H)) (syn_c1c))).fv ∪ ((Class.cv (nb072_alpha_dummy_134 y H))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0134 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_132 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0135 (y : Var) (H : Class) : (nb072_alpha_dummy_134 y H) ∈ (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0136 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_139 A B R S_cls H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0137 (y : Var) (H : Class) : (nb072_alpha_dummy_142 y H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H)) (Class.cv (nb072_alpha_dummy_143 y H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H)) (Class.cv (nb072_alpha_dummy_143 y H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0138 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_139 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0139 (y : Var) (H : Class) : (nb072_alpha_dummy_142 y H) ∈ (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_143 y H))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0140 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_140 A B R S_cls H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_139 A B R S_cls H)) (Class.cv (nb072_alpha_dummy_140 A B R S_cls H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0141 (y : Var) (H : Class) : (nb072_alpha_dummy_143 y H) ∈ (((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H)) (Class.cv (nb072_alpha_dummy_143 y H)))).fv ∪ ((syn_cnin (Class.cv (nb072_alpha_dummy_142 y H)) (Class.cv (nb072_alpha_dummy_143 y H)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0142 (A : Class) (B : Class) (R : Class) (S_cls : Class) (H : Class) : (nb072_alpha_dummy_140 A B R S_cls H) ∈ (((Class.cv (nb072_alpha_dummy_139 A B R S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_140 A B R S_cls H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb072_support_mem_0143 (y : Var) (H : Class) : (nb072_alpha_dummy_143 y H) ∈ (((Class.cv (nb072_alpha_dummy_142 y H))).fv ∪ ((Class.cv (nb072_alpha_dummy_143 y H))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
