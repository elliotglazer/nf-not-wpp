import NAR4C079C001Part001

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

theorem nb079_support_mem_0019 (x : Var) (y : Var) : y ∈ (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪ ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0020 (A : Class) : (nb079_alpha_dummy_001 A) ∈ (((syn_cpr (Class.cv (nb079_alpha_dummy_000 A)) (Class.cv (nb079_alpha_dummy_001 A)))).fv) := by
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0021 (x : Var) (y : Var) : y ∈ (((syn_cpr (Class.cv x) (Class.cv y))).fv) := by
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0022 (A : Class) : (nb079_alpha_dummy_001 A) ∈ (((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_000 A))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb079_alpha_dummy_001 A))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0023 (x : Var) (y : Var) : y ∈ (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0024 (A : Class) : (nb079_alpha_dummy_001 A) ∈ (((syn_csn (Class.cv (nb079_alpha_dummy_001 A)))).fv ∪ ((syn_csn (Class.cv (nb079_alpha_dummy_001 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0025 (y : Var) : y ∈ (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0026 (A : Class) : (nb079_alpha_dummy_001 A) ∈ (((Class.cv (nb079_alpha_dummy_001 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0027 (y : Var) : y ∈ (((Class.cv y)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0028 (A : Class) : (nb079_alpha_dummy_000 A) ∈ (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_001 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0029 (A : Class) : (nb079_alpha_dummy_000 A) ∈ (((syn_ccompl (Class.cab (nb079_alpha_dummy_023 A) (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A)) (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A)) (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb079_alpha_dummy_023 A) (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A)) (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0030 (x : Var) (y : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0031 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb079_alpha_dummy_025 x y) (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x) (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y)) (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb079_alpha_dummy_025 x y) (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y) (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y)) (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0032 (A : Class) : (nb079_alpha_dummy_000 A) ∈ (((Class.cab (nb079_alpha_dummy_023 A) (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A)) (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A)) (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_023 A) (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A)) (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A)) (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0028 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0033 (x : Var) (y : Var) : x ∈ (((Class.cab (nb079_alpha_dummy_025 x y) (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x) (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y)) (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_025 x y) (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x) (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y)) (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0030 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0034 (A : Class) : (nb079_alpha_dummy_024 A) ∈ (((Class.cv (nb079_alpha_dummy_024 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0035 (x : Var) (y : Var) : (nb079_alpha_dummy_026 x y) ∈ (((Class.cv (nb079_alpha_dummy_026 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0036 (A : Class) : (nb079_alpha_dummy_031 A) ∈ (((Wff.classMem (Class.cv (nb079_alpha_dummy_031 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb079_alpha_dummy_031 A)) (syn_c1c))).fv ∪ ((Class.cv (nb079_alpha_dummy_031 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0037 (x : Var) (y : Var) : (nb079_alpha_dummy_033 x y) ∈ (((Wff.classMem (Class.cv (nb079_alpha_dummy_033 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb079_alpha_dummy_033 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb079_alpha_dummy_033 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0038 (A : Class) : (nb079_alpha_dummy_031 A) ∈ (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0039 (x : Var) (y : Var) : (nb079_alpha_dummy_033 x y) ∈ (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0040 (A : Class) : (nb079_alpha_dummy_038 A) ∈ (((syn_cnin (Class.cv (nb079_alpha_dummy_038 A)) (Class.cv (nb079_alpha_dummy_039 A)))).fv ∪ ((syn_cnin (Class.cv (nb079_alpha_dummy_038 A)) (Class.cv (nb079_alpha_dummy_039 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0041 (x : Var) (y : Var) : (nb079_alpha_dummy_041 x y) ∈ (((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y)) (Class.cv (nb079_alpha_dummy_042 x y)))).fv ∪ ((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y)) (Class.cv (nb079_alpha_dummy_042 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0042 (A : Class) : (nb079_alpha_dummy_038 A) ∈ (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_039 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0043 (x : Var) (y : Var) : (nb079_alpha_dummy_041 x y) ∈ (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪ ((Class.cv (nb079_alpha_dummy_042 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0044 (A : Class) : (nb079_alpha_dummy_039 A) ∈ (((syn_cnin (Class.cv (nb079_alpha_dummy_038 A)) (Class.cv (nb079_alpha_dummy_039 A)))).fv ∪ ((syn_cnin (Class.cv (nb079_alpha_dummy_038 A)) (Class.cv (nb079_alpha_dummy_039 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0045 (x : Var) (y : Var) : (nb079_alpha_dummy_042 x y) ∈ (((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y)) (Class.cv (nb079_alpha_dummy_042 x y)))).fv ∪ ((syn_cnin (Class.cv (nb079_alpha_dummy_041 x y)) (Class.cv (nb079_alpha_dummy_042 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0046 (A : Class) : (nb079_alpha_dummy_039 A) ∈ (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_039 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0047 (x : Var) (y : Var) : (nb079_alpha_dummy_042 x y) ∈ (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪ ((Class.cv (nb079_alpha_dummy_042 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0048 (A : Class) : (nb079_alpha_dummy_038 A) ∈ (((syn_ccompl (Class.cv (nb079_alpha_dummy_038 A)))).fv ∪ ((syn_ccompl (Class.cv (nb079_alpha_dummy_039 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0049 (x : Var) (y : Var) : (nb079_alpha_dummy_041 x y) ∈ (((syn_ccompl (Class.cv (nb079_alpha_dummy_041 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb079_alpha_dummy_042 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0050 (A : Class) : (nb079_alpha_dummy_038 A) ∈ (((Class.cv (nb079_alpha_dummy_038 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_038 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0051 (x : Var) (y : Var) : (nb079_alpha_dummy_041 x y) ∈ (((Class.cv (nb079_alpha_dummy_041 x y))).fv ∪ ((Class.cv (nb079_alpha_dummy_041 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0052 (A : Class) : (nb079_alpha_dummy_039 A) ∈ (((syn_ccompl (Class.cv (nb079_alpha_dummy_038 A)))).fv ∪ ((syn_ccompl (Class.cv (nb079_alpha_dummy_039 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0053 (x : Var) (y : Var) : (nb079_alpha_dummy_042 x y) ∈ (((syn_ccompl (Class.cv (nb079_alpha_dummy_041 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb079_alpha_dummy_042 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0054 (A : Class) : (nb079_alpha_dummy_039 A) ∈ (((Class.cv (nb079_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_039 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0055 (x : Var) (y : Var) : (nb079_alpha_dummy_042 x y) ∈ (((Class.cv (nb079_alpha_dummy_042 x y))).fv ∪ ((Class.cv (nb079_alpha_dummy_042 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0056 (A : Class) : (nb079_alpha_dummy_001 A) ∈ (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb079_alpha_dummy_001 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0057 (A : Class) : (nb079_alpha_dummy_001 A) ∈ (((syn_ccompl (Class.cab (nb079_alpha_dummy_023 A) (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_000 A)) (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A)) (syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb079_alpha_dummy_023 A) (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A)) (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0058 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0059 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb079_alpha_dummy_025 x y) (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv x) (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y)) (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb079_alpha_dummy_025 x y) (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y) (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y)) (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0060 (A : Class) : (nb079_alpha_dummy_001 A) ∈ (((Class.cab (nb079_alpha_dummy_023 A) (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A)) (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_023 A) (syn_wrex (nb079_alpha_dummy_024 A) (Class.cv (nb079_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb079_alpha_dummy_023 A)) (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0056 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0061 (x : Var) (y : Var) : y ∈ (((Class.cab (nb079_alpha_dummy_025 x y) (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y) (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y)) (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb079_alpha_dummy_025 x y) (syn_wrex (nb079_alpha_dummy_026 x y) (Class.cv y) (Wff.classEq (Class.cv (nb079_alpha_dummy_025 x y)) (syn_cun (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb079_support_mem_0058 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb079_support_mem_0062 (A : Class) : (nb079_alpha_dummy_024 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb079_alpha_dummy_024 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0063 (x : Var) (y : Var) : (nb079_alpha_dummy_026 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb079_alpha_dummy_026 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0064 (A : Class) : (nb079_alpha_dummy_024 A) ∈ (((syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))).fv ∪ ((syn_cphi (Class.cv (nb079_alpha_dummy_024 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_support_mem_0065 (x : Var) (y : Var) : (nb079_alpha_dummy_026 x y) ∈ (((syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))).fv ∪ ((syn_cphi (Class.cv (nb079_alpha_dummy_026 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb079_compact_fv_empty_0000 (A : Class) : (nb079_alpha_dummy_039 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0000 (A : Class) : (nb079_alpha_dummy_039 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_039, fv_syn_c1c] using (nb079_compact_fv_empty_0000 A)

theorem nb079_compact_fv_empty_0001 (x : Var) (y : Var) : (nb079_alpha_dummy_042 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0001 (x : Var) (y : Var) : (nb079_alpha_dummy_042 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_042, fv_syn_c1c] using (nb079_compact_fv_empty_0001 x y)

theorem nb079_compact_fv_empty_0002 (A : Class) : (nb079_alpha_dummy_038 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0002 (A : Class) : (nb079_alpha_dummy_038 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_038, fv_syn_c1c] using (nb079_compact_fv_empty_0002 A)

theorem nb079_compact_fv_empty_0003 (x : Var) (y : Var) : (nb079_alpha_dummy_041 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0003 (x : Var) (y : Var) : (nb079_alpha_dummy_041 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_041, fv_syn_c1c] using (nb079_compact_fv_empty_0003 x y)

theorem nb079_compact_fv_empty_0004 (A : Class) : (nb079_alpha_dummy_037 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0004 (A : Class) : (nb079_alpha_dummy_037 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_037, fv_syn_c1c] using (nb079_compact_fv_empty_0004 A)

theorem nb079_compact_fv_empty_0005 (x : Var) (y : Var) : (nb079_alpha_dummy_040 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0005 (x : Var) (y : Var) : (nb079_alpha_dummy_040 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_040, fv_syn_c1c] using (nb079_compact_fv_empty_0005 x y)

theorem nb079_compact_fv_empty_0006 (A : Class) : (nb079_alpha_dummy_035 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0006 (A : Class) : (nb079_alpha_dummy_035 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_035, fv_syn_c1c] using (nb079_compact_fv_empty_0006 A)

theorem nb079_compact_fv_empty_0007 (x : Var) (y : Var) : (nb079_alpha_dummy_036 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0007 (x : Var) (y : Var) : (nb079_alpha_dummy_036 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_036, fv_syn_c1c] using (nb079_compact_fv_empty_0007 x y)

theorem nb079_compact_fv_empty_0008 (A : Class) : (nb079_alpha_dummy_031 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0008 (A : Class) : (nb079_alpha_dummy_031 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_031, fv_syn_c1c] using (nb079_compact_fv_empty_0008 A)

theorem nb079_compact_fv_empty_0009 (x : Var) (y : Var) : (nb079_alpha_dummy_033 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0009 (x : Var) (y : Var) : (nb079_alpha_dummy_033 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_033, fv_syn_c1c] using (nb079_compact_fv_empty_0009 x y)

theorem nb079_compact_fv_empty_0010 (A : Class) : (nb079_alpha_dummy_032 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0010 (A : Class) : (nb079_alpha_dummy_032 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_032, fv_syn_c1c] using (nb079_compact_fv_empty_0010 A)

theorem nb079_compact_fv_empty_0011 (x : Var) (y : Var) : (nb079_alpha_dummy_034 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0011 (x : Var) (y : Var) : (nb079_alpha_dummy_034 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_034, fv_syn_c1c] using (nb079_compact_fv_empty_0011 x y)

theorem nb079_compact_fv_empty_0012 (A : Class) : (nb079_alpha_dummy_024 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0012 (A : Class) : (nb079_alpha_dummy_024 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_024, fv_syn_c1c] using (nb079_compact_fv_empty_0012 A)

theorem nb079_compact_fv_empty_0013 (x : Var) (y : Var) : (nb079_alpha_dummy_026 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0013 (x : Var) (y : Var) : (nb079_alpha_dummy_026 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_026, fv_syn_c1c] using (nb079_compact_fv_empty_0013 x y)

theorem nb079_compact_fv_empty_0014 (A : Class) : (nb079_alpha_dummy_023 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0014 (A : Class) : (nb079_alpha_dummy_023 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_023, fv_syn_c1c] using (nb079_compact_fv_empty_0014 A)

theorem nb079_compact_fv_empty_0015 (x : Var) (y : Var) : (nb079_alpha_dummy_025 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0015 (x : Var) (y : Var) : (nb079_alpha_dummy_025 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_025, fv_syn_c1c] using (nb079_compact_fv_empty_0015 x y)

theorem nb079_compact_fv_empty_0016 (A : Class) : (nb079_alpha_dummy_029 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0016 (A : Class) : (nb079_alpha_dummy_029 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_029, fv_syn_c1c] using (nb079_compact_fv_empty_0016 A)

theorem nb079_compact_fv_empty_0017 (x : Var) (y : Var) : (nb079_alpha_dummy_030 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0017 (x : Var) (y : Var) : (nb079_alpha_dummy_030 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_030, fv_syn_c1c] using (nb079_compact_fv_empty_0017 x y)

theorem nb079_compact_fv_empty_0018 (A : Class) : (nb079_alpha_dummy_027 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0018 (A : Class) : (nb079_alpha_dummy_027 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_027, fv_syn_c1c] using (nb079_compact_fv_empty_0018 A)

theorem nb079_compact_fv_empty_0019 (x : Var) (y : Var) : (nb079_alpha_dummy_028 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0019 (x : Var) (y : Var) : (nb079_alpha_dummy_028 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_028, fv_syn_c1c] using (nb079_compact_fv_empty_0019 x y)

theorem nb079_compact_fv_empty_0020 (A : Class) : (nb079_alpha_dummy_001 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0020 (A : Class) : (nb079_alpha_dummy_001 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_001, fv_syn_c1c] using (nb079_compact_fv_empty_0020 A)

theorem nb079_compact_fv_empty_0021 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0021 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb079_compact_fv_empty_0021 y)

theorem nb079_compact_fv_empty_0022 (A : Class) : (nb079_alpha_dummy_000 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0022 (A : Class) : (nb079_alpha_dummy_000 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_000, fv_syn_c1c] using (nb079_compact_fv_empty_0022 A)

theorem nb079_compact_fv_empty_0023 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0023 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb079_compact_fv_empty_0023 x)

theorem nb079_compact_fv_empty_0024 (A : Class) : (nb079_alpha_dummy_002 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0024 (A : Class) : (nb079_alpha_dummy_002 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb079_alpha_dummy_002, fv_syn_c1c] using (nb079_compact_fv_empty_0024 A)

theorem nb079_compact_fv_empty_0025 (z : Var) : z ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb079_wpp_notmem_0025 (z : Var) : z ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb079_compact_fv_empty_0025 z)

theorem nb079_compact_envfresh_0000 (x : Var) (y : Var) (z : Var) (A : Class) : TEnvFresh [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A), (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)), ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb079_alpha_dummy_039 A) (nb079_alpha_dummy_042 x y) (nb079_wpp_notmem_0000 A) (nb079_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_038 A) (nb079_alpha_dummy_041 x y) (nb079_wpp_notmem_0002 A) (nb079_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_037 A) (nb079_alpha_dummy_040 x y) (nb079_wpp_notmem_0004 A) (nb079_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_035 A) (nb079_alpha_dummy_036 x y) (nb079_wpp_notmem_0006 A) (nb079_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_031 A) (nb079_alpha_dummy_033 x y) (nb079_wpp_notmem_0008 A) (nb079_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_032 A) (nb079_alpha_dummy_034 x y) (nb079_wpp_notmem_0010 A) (nb079_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_024 A) (nb079_alpha_dummy_026 x y) (nb079_wpp_notmem_0012 A) (nb079_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_023 A) (nb079_alpha_dummy_025 x y) (nb079_wpp_notmem_0014 A) (nb079_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_029 A) (nb079_alpha_dummy_030 x y) (nb079_wpp_notmem_0016 A) (nb079_wpp_notmem_0017 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_027 A) (nb079_alpha_dummy_028 x y) (nb079_wpp_notmem_0018 A) (nb079_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_001 A) y (nb079_wpp_notmem_0020 A) (nb079_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb079_alpha_dummy_000 A) x (nb079_wpp_notmem_0022 A) (nb079_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb079_alpha_dummy_002 A) z (nb079_wpp_notmem_0024 A) (nb079_wpp_notmem_0025 z) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb079_wpp_refl_0000 (x : Var) (y : Var) (z : Var) (A : Class) : TReflOn [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A), (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)), ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb079_compact_envfresh_0000 x y z A)

theorem nb079_wpp_notmem_0026 (A : Class) : (nb079_alpha_dummy_039 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_039, fv_syn_c0] using (nb079_compact_fv_empty_0000 A)

theorem nb079_wpp_notmem_0027 (x : Var) (y : Var) : (nb079_alpha_dummy_042 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_042, fv_syn_c0] using (nb079_compact_fv_empty_0001 x y)

theorem nb079_wpp_notmem_0028 (A : Class) : (nb079_alpha_dummy_038 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_038, fv_syn_c0] using (nb079_compact_fv_empty_0002 A)

theorem nb079_wpp_notmem_0029 (x : Var) (y : Var) : (nb079_alpha_dummy_041 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_041, fv_syn_c0] using (nb079_compact_fv_empty_0003 x y)

theorem nb079_wpp_notmem_0030 (A : Class) : (nb079_alpha_dummy_037 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_037, fv_syn_c0] using (nb079_compact_fv_empty_0004 A)

theorem nb079_wpp_notmem_0031 (x : Var) (y : Var) : (nb079_alpha_dummy_040 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_040, fv_syn_c0] using (nb079_compact_fv_empty_0005 x y)

theorem nb079_wpp_notmem_0032 (A : Class) : (nb079_alpha_dummy_035 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_035, fv_syn_c0] using (nb079_compact_fv_empty_0006 A)

theorem nb079_wpp_notmem_0033 (x : Var) (y : Var) : (nb079_alpha_dummy_036 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_036, fv_syn_c0] using (nb079_compact_fv_empty_0007 x y)

theorem nb079_wpp_notmem_0034 (A : Class) : (nb079_alpha_dummy_031 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_031, fv_syn_c0] using (nb079_compact_fv_empty_0008 A)

theorem nb079_wpp_notmem_0035 (x : Var) (y : Var) : (nb079_alpha_dummy_033 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_033, fv_syn_c0] using (nb079_compact_fv_empty_0009 x y)

theorem nb079_wpp_notmem_0036 (A : Class) : (nb079_alpha_dummy_032 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_032, fv_syn_c0] using (nb079_compact_fv_empty_0010 A)

theorem nb079_wpp_notmem_0037 (x : Var) (y : Var) : (nb079_alpha_dummy_034 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_034, fv_syn_c0] using (nb079_compact_fv_empty_0011 x y)

theorem nb079_wpp_notmem_0038 (A : Class) : (nb079_alpha_dummy_024 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_024, fv_syn_c0] using (nb079_compact_fv_empty_0012 A)

theorem nb079_wpp_notmem_0039 (x : Var) (y : Var) : (nb079_alpha_dummy_026 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_026, fv_syn_c0] using (nb079_compact_fv_empty_0013 x y)

theorem nb079_wpp_notmem_0040 (A : Class) : (nb079_alpha_dummy_023 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_023, fv_syn_c0] using (nb079_compact_fv_empty_0014 A)

theorem nb079_wpp_notmem_0041 (x : Var) (y : Var) : (nb079_alpha_dummy_025 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_025, fv_syn_c0] using (nb079_compact_fv_empty_0015 x y)

theorem nb079_wpp_notmem_0042 (A : Class) : (nb079_alpha_dummy_029 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_029, fv_syn_c0] using (nb079_compact_fv_empty_0016 A)

theorem nb079_wpp_notmem_0043 (x : Var) (y : Var) : (nb079_alpha_dummy_030 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_030, fv_syn_c0] using (nb079_compact_fv_empty_0017 x y)

theorem nb079_wpp_notmem_0044 (A : Class) : (nb079_alpha_dummy_027 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_027, fv_syn_c0] using (nb079_compact_fv_empty_0018 A)

theorem nb079_wpp_notmem_0045 (x : Var) (y : Var) : (nb079_alpha_dummy_028 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_028, fv_syn_c0] using (nb079_compact_fv_empty_0019 x y)

theorem nb079_wpp_notmem_0046 (A : Class) : (nb079_alpha_dummy_001 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_001, fv_syn_c0] using (nb079_compact_fv_empty_0020 A)

theorem nb079_wpp_notmem_0047 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb079_compact_fv_empty_0021 y)

theorem nb079_wpp_notmem_0048 (A : Class) : (nb079_alpha_dummy_000 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_000, fv_syn_c0] using (nb079_compact_fv_empty_0022 A)

theorem nb079_wpp_notmem_0049 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb079_compact_fv_empty_0023 x)

theorem nb079_wpp_notmem_0050 (A : Class) : (nb079_alpha_dummy_002 A) ∉ ((syn_c0)).fv := by
  simpa only [nb079_alpha_dummy_002, fv_syn_c0] using (nb079_compact_fv_empty_0024 A)

theorem nb079_wpp_notmem_0051 (z : Var) : z ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb079_compact_fv_empty_0025 z)

theorem nb079_compact_envfresh_0001 (x : Var) (y : Var) (z : Var) (A : Class) : TEnvFresh [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A), (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)), ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb079_alpha_dummy_039 A) (nb079_alpha_dummy_042 x y) (nb079_wpp_notmem_0026 A) (nb079_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_038 A) (nb079_alpha_dummy_041 x y) (nb079_wpp_notmem_0028 A) (nb079_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_037 A) (nb079_alpha_dummy_040 x y) (nb079_wpp_notmem_0030 A) (nb079_wpp_notmem_0031 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_035 A) (nb079_alpha_dummy_036 x y) (nb079_wpp_notmem_0032 A) (nb079_wpp_notmem_0033 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_031 A) (nb079_alpha_dummy_033 x y) (nb079_wpp_notmem_0034 A) (nb079_wpp_notmem_0035 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_032 A) (nb079_alpha_dummy_034 x y) (nb079_wpp_notmem_0036 A) (nb079_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_024 A) (nb079_alpha_dummy_026 x y) (nb079_wpp_notmem_0038 A) (nb079_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_023 A) (nb079_alpha_dummy_025 x y) (nb079_wpp_notmem_0040 A) (nb079_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_029 A) (nb079_alpha_dummy_030 x y) (nb079_wpp_notmem_0042 A) (nb079_wpp_notmem_0043 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_027 A) (nb079_alpha_dummy_028 x y) (nb079_wpp_notmem_0044 A) (nb079_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_001 A) y (nb079_wpp_notmem_0046 A) (nb079_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb079_alpha_dummy_000 A) x (nb079_wpp_notmem_0048 A) (nb079_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb079_alpha_dummy_002 A) z (nb079_wpp_notmem_0050 A) (nb079_wpp_notmem_0051 z) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb079_wpp_refl_0001 (x : Var) (y : Var) (z : Var) (A : Class) : TReflOn [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A), (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)), ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb079_compact_envfresh_0001 x y z A)

theorem nb079_wpp_notmem_0052 (A : Class) : (nb079_alpha_dummy_035 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_035, fv_syn_cnnc] using (nb079_compact_fv_empty_0006 A)

theorem nb079_wpp_notmem_0053 (x : Var) (y : Var) : (nb079_alpha_dummy_036 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_036, fv_syn_cnnc] using (nb079_compact_fv_empty_0007 x y)

theorem nb079_wpp_notmem_0054 (A : Class) : (nb079_alpha_dummy_031 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_031, fv_syn_cnnc] using (nb079_compact_fv_empty_0008 A)

theorem nb079_wpp_notmem_0055 (x : Var) (y : Var) : (nb079_alpha_dummy_033 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_033, fv_syn_cnnc] using (nb079_compact_fv_empty_0009 x y)

theorem nb079_wpp_notmem_0056 (A : Class) : (nb079_alpha_dummy_032 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_032, fv_syn_cnnc] using (nb079_compact_fv_empty_0010 A)

theorem nb079_wpp_notmem_0057 (x : Var) (y : Var) : (nb079_alpha_dummy_034 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_034, fv_syn_cnnc] using (nb079_compact_fv_empty_0011 x y)

theorem nb079_wpp_notmem_0058 (A : Class) : (nb079_alpha_dummy_024 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_024, fv_syn_cnnc] using (nb079_compact_fv_empty_0012 A)

theorem nb079_wpp_notmem_0059 (x : Var) (y : Var) : (nb079_alpha_dummy_026 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_026, fv_syn_cnnc] using (nb079_compact_fv_empty_0013 x y)

theorem nb079_wpp_notmem_0060 (A : Class) : (nb079_alpha_dummy_023 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_023, fv_syn_cnnc] using (nb079_compact_fv_empty_0014 A)

theorem nb079_wpp_notmem_0061 (x : Var) (y : Var) : (nb079_alpha_dummy_025 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_025, fv_syn_cnnc] using (nb079_compact_fv_empty_0015 x y)

theorem nb079_wpp_notmem_0062 (A : Class) : (nb079_alpha_dummy_029 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_029, fv_syn_cnnc] using (nb079_compact_fv_empty_0016 A)

theorem nb079_wpp_notmem_0063 (x : Var) (y : Var) : (nb079_alpha_dummy_030 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_030, fv_syn_cnnc] using (nb079_compact_fv_empty_0017 x y)

theorem nb079_wpp_notmem_0064 (A : Class) : (nb079_alpha_dummy_027 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_027, fv_syn_cnnc] using (nb079_compact_fv_empty_0018 A)

theorem nb079_wpp_notmem_0065 (x : Var) (y : Var) : (nb079_alpha_dummy_028 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_028, fv_syn_cnnc] using (nb079_compact_fv_empty_0019 x y)

theorem nb079_wpp_notmem_0066 (A : Class) : (nb079_alpha_dummy_001 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_001, fv_syn_cnnc] using (nb079_compact_fv_empty_0020 A)

theorem nb079_wpp_notmem_0067 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb079_compact_fv_empty_0021 y)

theorem nb079_wpp_notmem_0068 (A : Class) : (nb079_alpha_dummy_000 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_000, fv_syn_cnnc] using (nb079_compact_fv_empty_0022 A)

theorem nb079_wpp_notmem_0069 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb079_compact_fv_empty_0023 x)

theorem nb079_wpp_notmem_0070 (A : Class) : (nb079_alpha_dummy_002 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb079_alpha_dummy_002, fv_syn_cnnc] using (nb079_compact_fv_empty_0024 A)

theorem nb079_wpp_notmem_0071 (z : Var) : z ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb079_compact_fv_empty_0025 z)

theorem nb079_compact_envfresh_0002 (x : Var) (y : Var) (z : Var) (A : Class) : TEnvFresh [((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A), (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)), ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A), (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)), ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb079_alpha_dummy_035 A) (nb079_alpha_dummy_036 x y) (nb079_wpp_notmem_0052 A) (nb079_wpp_notmem_0053 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_031 A) (nb079_alpha_dummy_033 x y) (nb079_wpp_notmem_0054 A) (nb079_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_032 A) (nb079_alpha_dummy_034 x y) (nb079_wpp_notmem_0056 A) (nb079_wpp_notmem_0057 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_024 A) (nb079_alpha_dummy_026 x y) (nb079_wpp_notmem_0058 A) (nb079_wpp_notmem_0059 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_023 A) (nb079_alpha_dummy_025 x y) (nb079_wpp_notmem_0060 A) (nb079_wpp_notmem_0061 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_029 A) (nb079_alpha_dummy_030 x y) (nb079_wpp_notmem_0062 A) (nb079_wpp_notmem_0063 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_027 A) (nb079_alpha_dummy_028 x y) (nb079_wpp_notmem_0064 A) (nb079_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb079_alpha_dummy_001 A) y (nb079_wpp_notmem_0066 A) (nb079_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb079_alpha_dummy_000 A) x (nb079_wpp_notmem_0068 A) (nb079_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb079_alpha_dummy_002 A) z (nb079_wpp_notmem_0070 A) (nb079_wpp_notmem_0071 z) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
