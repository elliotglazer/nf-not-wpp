import NAR4C081C001Part001

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

theorem nb081_support_mem_0019 (x : Var) (y : Var) : (nb081_alpha_dummy_022 x y) ∈ (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪ ((Class.cv (nb081_alpha_dummy_023 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0020 (A : Class) : (nb081_alpha_dummy_020 A) ∈ (((syn_cnin (Class.cv (nb081_alpha_dummy_019 A)) (Class.cv (nb081_alpha_dummy_020 A)))).fv ∪ ((syn_cnin (Class.cv (nb081_alpha_dummy_019 A)) (Class.cv (nb081_alpha_dummy_020 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0021 (x : Var) (y : Var) : (nb081_alpha_dummy_023 x y) ∈ (((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y)) (Class.cv (nb081_alpha_dummy_023 x y)))).fv ∪ ((syn_cnin (Class.cv (nb081_alpha_dummy_022 x y)) (Class.cv (nb081_alpha_dummy_023 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0022 (A : Class) : (nb081_alpha_dummy_020 A) ∈ (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_020 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0023 (x : Var) (y : Var) : (nb081_alpha_dummy_023 x y) ∈ (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪ ((Class.cv (nb081_alpha_dummy_023 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0024 (A : Class) : (nb081_alpha_dummy_019 A) ∈ (((syn_ccompl (Class.cv (nb081_alpha_dummy_019 A)))).fv ∪ ((syn_ccompl (Class.cv (nb081_alpha_dummy_020 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0025 (x : Var) (y : Var) : (nb081_alpha_dummy_022 x y) ∈ (((syn_ccompl (Class.cv (nb081_alpha_dummy_022 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb081_alpha_dummy_023 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0026 (A : Class) : (nb081_alpha_dummy_019 A) ∈ (((Class.cv (nb081_alpha_dummy_019 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_019 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0027 (x : Var) (y : Var) : (nb081_alpha_dummy_022 x y) ∈ (((Class.cv (nb081_alpha_dummy_022 x y))).fv ∪ ((Class.cv (nb081_alpha_dummy_022 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0028 (A : Class) : (nb081_alpha_dummy_020 A) ∈ (((syn_ccompl (Class.cv (nb081_alpha_dummy_019 A)))).fv ∪ ((syn_ccompl (Class.cv (nb081_alpha_dummy_020 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0029 (x : Var) (y : Var) : (nb081_alpha_dummy_023 x y) ∈ (((syn_ccompl (Class.cv (nb081_alpha_dummy_022 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb081_alpha_dummy_023 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0030 (A : Class) : (nb081_alpha_dummy_020 A) ∈ (((Class.cv (nb081_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_020 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0031 (x : Var) (y : Var) : (nb081_alpha_dummy_023 x y) ∈ (((Class.cv (nb081_alpha_dummy_023 x y))).fv ∪ ((Class.cv (nb081_alpha_dummy_023 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0032 (A : Class) : (nb081_alpha_dummy_001 A) ∈ (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb081_alpha_dummy_001 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0033 (A : Class) : (nb081_alpha_dummy_001 A) ∈ (((syn_ccompl (Class.cab (nb081_alpha_dummy_004 A) (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_000 A)) (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A)) (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb081_alpha_dummy_004 A) (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A)) (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0034 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0035 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb081_alpha_dummy_006 x y) (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv x) (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y)) (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb081_alpha_dummy_006 x y) (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y) (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y)) (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0036 (A : Class) : (nb081_alpha_dummy_001 A) ∈ (((Class.cab (nb081_alpha_dummy_004 A) (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A)) (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb081_alpha_dummy_004 A) (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A)) (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0037 (x : Var) (y : Var) : y ∈ (((Class.cab (nb081_alpha_dummy_006 x y) (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y) (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y)) (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb081_alpha_dummy_006 x y) (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y) (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y)) (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0034 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb081_support_mem_0038 (A : Class) : (nb081_alpha_dummy_005 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb081_alpha_dummy_005 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0039 (x : Var) (y : Var) : (nb081_alpha_dummy_007 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0040 (A : Class) : (nb081_alpha_dummy_005 A) ∈ (((syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))).fv ∪ ((syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0041 (x : Var) (y : Var) : (nb081_alpha_dummy_007 x y) ∈ (((syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))).fv ∪ ((syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0042 (A : Class) : (nb081_alpha_dummy_000 A) ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A)))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0043 (x : Var) (y : Var) : x ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv x))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv x) (Class.cv y))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0044 (A : Class) : (nb081_alpha_dummy_000 A) ∈ (((syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪ ((syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0045 (x : Var) : x ∈ (((syn_csn (syn_csn (Class.cv x)))).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0046 (A : Class) : (nb081_alpha_dummy_000 A) ∈ (((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv) := by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0047 (x : Var) : x ∈ (((syn_csn (Class.cv x))).fv) := by
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0048 (A : Class) : (nb081_alpha_dummy_000 A) ∈ (((Class.cv (nb081_alpha_dummy_000 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0049 (x : Var) : x ∈ (((Class.cv x)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0050 (A : Class) : (nb081_alpha_dummy_000 A) ∈ (((syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0051 (x : Var) (y : Var) : x ∈ (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪ ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0052 (A : Class) : (nb081_alpha_dummy_000 A) ∈ (((syn_cpr (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A)))).fv) := by
  rw [fv_syn_cpr]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0053 (x : Var) (y : Var) : x ∈ (((syn_cpr (Class.cv x) (Class.cv y))).fv) := by
  rw [fv_syn_cpr]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0054 (A : Class) : (nb081_alpha_dummy_000 A) ∈ (((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_001 A))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0055 (x : Var) (y : Var) : x ∈ (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0056 (A : Class) : (nb081_alpha_dummy_000 A) ∈ (((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv ∪ ((syn_csn (Class.cv (nb081_alpha_dummy_000 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0057 (x : Var) : x ∈ (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0058 (A : Class) : (nb081_alpha_dummy_001 A) ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv (nb081_alpha_dummy_000 A)))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0059 (x : Var) (y : Var) : y ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv x))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv x) (Class.cv y))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0060 (A : Class) : (nb081_alpha_dummy_001 A) ∈ (((syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A))))).fv ∪ ((syn_csn (syn_cpr (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0061 (x : Var) (y : Var) : y ∈ (((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv ∪ ((syn_csn (syn_cpr (Class.cv x) (Class.cv y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0062 (A : Class) : (nb081_alpha_dummy_001 A) ∈ (((syn_cpr (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A)))).fv) := by
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0063 (x : Var) (y : Var) : y ∈ (((syn_cpr (Class.cv x) (Class.cv y))).fv) := by
  rw [fv_syn_cpr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0064 (A : Class) : (nb081_alpha_dummy_001 A) ∈ (((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_000 A))))).fv ∪ ((syn_ccompl (syn_csn (Class.cv (nb081_alpha_dummy_001 A))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0065 (x : Var) (y : Var) : y ∈ (((syn_ccompl (syn_csn (Class.cv x)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0066 (A : Class) : (nb081_alpha_dummy_001 A) ∈ (((syn_csn (Class.cv (nb081_alpha_dummy_001 A)))).fv ∪ ((syn_csn (Class.cv (nb081_alpha_dummy_001 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0067 (y : Var) : y ∈ (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0068 (A : Class) : (nb081_alpha_dummy_001 A) ∈ (((Class.cv (nb081_alpha_dummy_001 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_support_mem_0069 (y : Var) : y ∈ (((Class.cv y)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb081_compact_fv_empty_0000 (A : Class) : (nb081_alpha_dummy_020 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0000 (A : Class) : (nb081_alpha_dummy_020 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_020, fv_syn_c1c] using (nb081_compact_fv_empty_0000 A)

theorem nb081_compact_fv_empty_0001 (x : Var) (y : Var) : (nb081_alpha_dummy_023 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0001 (x : Var) (y : Var) : (nb081_alpha_dummy_023 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_023, fv_syn_c1c] using (nb081_compact_fv_empty_0001 x y)

theorem nb081_compact_fv_empty_0002 (A : Class) : (nb081_alpha_dummy_019 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0002 (A : Class) : (nb081_alpha_dummy_019 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_019, fv_syn_c1c] using (nb081_compact_fv_empty_0002 A)

theorem nb081_compact_fv_empty_0003 (x : Var) (y : Var) : (nb081_alpha_dummy_022 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0003 (x : Var) (y : Var) : (nb081_alpha_dummy_022 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_022, fv_syn_c1c] using (nb081_compact_fv_empty_0003 x y)

theorem nb081_compact_fv_empty_0004 (A : Class) : (nb081_alpha_dummy_018 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0004 (A : Class) : (nb081_alpha_dummy_018 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_018, fv_syn_c1c] using (nb081_compact_fv_empty_0004 A)

theorem nb081_compact_fv_empty_0005 (x : Var) (y : Var) : (nb081_alpha_dummy_021 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0005 (x : Var) (y : Var) : (nb081_alpha_dummy_021 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_021, fv_syn_c1c] using (nb081_compact_fv_empty_0005 x y)

theorem nb081_compact_fv_empty_0006 (A : Class) : (nb081_alpha_dummy_016 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0006 (A : Class) : (nb081_alpha_dummy_016 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_016, fv_syn_c1c] using (nb081_compact_fv_empty_0006 A)

theorem nb081_compact_fv_empty_0007 (x : Var) (y : Var) : (nb081_alpha_dummy_017 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0007 (x : Var) (y : Var) : (nb081_alpha_dummy_017 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_017, fv_syn_c1c] using (nb081_compact_fv_empty_0007 x y)

theorem nb081_compact_fv_empty_0008 (A : Class) : (nb081_alpha_dummy_012 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0008 (A : Class) : (nb081_alpha_dummy_012 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_012, fv_syn_c1c] using (nb081_compact_fv_empty_0008 A)

theorem nb081_compact_fv_empty_0009 (x : Var) (y : Var) : (nb081_alpha_dummy_014 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0009 (x : Var) (y : Var) : (nb081_alpha_dummy_014 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_014, fv_syn_c1c] using (nb081_compact_fv_empty_0009 x y)

theorem nb081_compact_fv_empty_0010 (A : Class) : (nb081_alpha_dummy_013 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0010 (A : Class) : (nb081_alpha_dummy_013 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_013, fv_syn_c1c] using (nb081_compact_fv_empty_0010 A)

theorem nb081_compact_fv_empty_0011 (x : Var) (y : Var) : (nb081_alpha_dummy_015 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0011 (x : Var) (y : Var) : (nb081_alpha_dummy_015 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_015, fv_syn_c1c] using (nb081_compact_fv_empty_0011 x y)

theorem nb081_compact_fv_empty_0012 (A : Class) : (nb081_alpha_dummy_005 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0012 (A : Class) : (nb081_alpha_dummy_005 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_005, fv_syn_c1c] using (nb081_compact_fv_empty_0012 A)

theorem nb081_compact_fv_empty_0013 (x : Var) (y : Var) : (nb081_alpha_dummy_007 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0013 (x : Var) (y : Var) : (nb081_alpha_dummy_007 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_007, fv_syn_c1c] using (nb081_compact_fv_empty_0013 x y)

theorem nb081_compact_fv_empty_0014 (A : Class) : (nb081_alpha_dummy_004 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0014 (A : Class) : (nb081_alpha_dummy_004 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_004, fv_syn_c1c] using (nb081_compact_fv_empty_0014 A)

theorem nb081_compact_fv_empty_0015 (x : Var) (y : Var) : (nb081_alpha_dummy_006 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0015 (x : Var) (y : Var) : (nb081_alpha_dummy_006 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_006, fv_syn_c1c] using (nb081_compact_fv_empty_0015 x y)

theorem nb081_compact_fv_empty_0016 (A : Class) : (nb081_alpha_dummy_010 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0016 (A : Class) : (nb081_alpha_dummy_010 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_010, fv_syn_c1c] using (nb081_compact_fv_empty_0016 A)

theorem nb081_compact_fv_empty_0017 (x : Var) (y : Var) : (nb081_alpha_dummy_011 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0017 (x : Var) (y : Var) : (nb081_alpha_dummy_011 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_011, fv_syn_c1c] using (nb081_compact_fv_empty_0017 x y)

theorem nb081_compact_fv_empty_0018 (A : Class) : (nb081_alpha_dummy_008 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0018 (A : Class) : (nb081_alpha_dummy_008 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_008, fv_syn_c1c] using (nb081_compact_fv_empty_0018 A)

theorem nb081_compact_fv_empty_0019 (x : Var) (y : Var) : (nb081_alpha_dummy_009 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0019 (x : Var) (y : Var) : (nb081_alpha_dummy_009 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_009, fv_syn_c1c] using (nb081_compact_fv_empty_0019 x y)

theorem nb081_compact_fv_empty_0020 (A : Class) : (nb081_alpha_dummy_001 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0020 (A : Class) : (nb081_alpha_dummy_001 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_001, fv_syn_c1c] using (nb081_compact_fv_empty_0020 A)

theorem nb081_compact_fv_empty_0021 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0021 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb081_compact_fv_empty_0021 y)

theorem nb081_compact_fv_empty_0022 (A : Class) : (nb081_alpha_dummy_000 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0022 (A : Class) : (nb081_alpha_dummy_000 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_000, fv_syn_c1c] using (nb081_compact_fv_empty_0022 A)

theorem nb081_compact_fv_empty_0023 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0023 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb081_compact_fv_empty_0023 x)

theorem nb081_compact_fv_empty_0024 (A : Class) : (nb081_alpha_dummy_002 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0024 (A : Class) : (nb081_alpha_dummy_002 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_002, fv_syn_c1c] using (nb081_compact_fv_empty_0024 A)

theorem nb081_compact_fv_empty_0025 (x : Var) (y : Var) (A : Class) : (nb081_alpha_dummy_003 x y A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb081_wpp_notmem_0025 (x : Var) (y : Var) (A : Class) : (nb081_alpha_dummy_003 x y A) ∉ ((syn_c1c)).fv := by
  simpa only [nb081_alpha_dummy_003, fv_syn_c1c] using (nb081_compact_fv_empty_0025 x y A)

theorem nb081_compact_envfresh_0000 (x : Var) (y : Var) (A : Class) : TEnvFresh [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A), (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)), ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A), (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)), ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb081_alpha_dummy_020 A) (nb081_alpha_dummy_023 x y) (nb081_wpp_notmem_0000 A) (nb081_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_019 A) (nb081_alpha_dummy_022 x y) (nb081_wpp_notmem_0002 A) (nb081_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_018 A) (nb081_alpha_dummy_021 x y) (nb081_wpp_notmem_0004 A) (nb081_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_016 A) (nb081_alpha_dummy_017 x y) (nb081_wpp_notmem_0006 A) (nb081_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_012 A) (nb081_alpha_dummy_014 x y) (nb081_wpp_notmem_0008 A) (nb081_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_013 A) (nb081_alpha_dummy_015 x y) (nb081_wpp_notmem_0010 A) (nb081_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_005 A) (nb081_alpha_dummy_007 x y) (nb081_wpp_notmem_0012 A) (nb081_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_004 A) (nb081_alpha_dummy_006 x y) (nb081_wpp_notmem_0014 A) (nb081_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_010 A) (nb081_alpha_dummy_011 x y) (nb081_wpp_notmem_0016 A) (nb081_wpp_notmem_0017 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_008 A) (nb081_alpha_dummy_009 x y) (nb081_wpp_notmem_0018 A) (nb081_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_001 A) y (nb081_wpp_notmem_0020 A) (nb081_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb081_alpha_dummy_000 A) x (nb081_wpp_notmem_0022 A) (nb081_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb081_alpha_dummy_002 A) (nb081_alpha_dummy_003 x y A) (nb081_wpp_notmem_0024 A) (nb081_wpp_notmem_0025 x y A) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb081_wpp_refl_0000 (x : Var) (y : Var) (A : Class) : TReflOn [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A), (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)), ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A), (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)), ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb081_compact_envfresh_0000 x y A)

theorem nb081_wpp_notmem_0026 (A : Class) : (nb081_alpha_dummy_020 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_020, fv_syn_c0] using (nb081_compact_fv_empty_0000 A)

theorem nb081_wpp_notmem_0027 (x : Var) (y : Var) : (nb081_alpha_dummy_023 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_023, fv_syn_c0] using (nb081_compact_fv_empty_0001 x y)

theorem nb081_wpp_notmem_0028 (A : Class) : (nb081_alpha_dummy_019 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_019, fv_syn_c0] using (nb081_compact_fv_empty_0002 A)

theorem nb081_wpp_notmem_0029 (x : Var) (y : Var) : (nb081_alpha_dummy_022 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_022, fv_syn_c0] using (nb081_compact_fv_empty_0003 x y)

theorem nb081_wpp_notmem_0030 (A : Class) : (nb081_alpha_dummy_018 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_018, fv_syn_c0] using (nb081_compact_fv_empty_0004 A)

theorem nb081_wpp_notmem_0031 (x : Var) (y : Var) : (nb081_alpha_dummy_021 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_021, fv_syn_c0] using (nb081_compact_fv_empty_0005 x y)

theorem nb081_wpp_notmem_0032 (A : Class) : (nb081_alpha_dummy_016 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_016, fv_syn_c0] using (nb081_compact_fv_empty_0006 A)

theorem nb081_wpp_notmem_0033 (x : Var) (y : Var) : (nb081_alpha_dummy_017 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_017, fv_syn_c0] using (nb081_compact_fv_empty_0007 x y)

theorem nb081_wpp_notmem_0034 (A : Class) : (nb081_alpha_dummy_012 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_012, fv_syn_c0] using (nb081_compact_fv_empty_0008 A)

theorem nb081_wpp_notmem_0035 (x : Var) (y : Var) : (nb081_alpha_dummy_014 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_014, fv_syn_c0] using (nb081_compact_fv_empty_0009 x y)

theorem nb081_wpp_notmem_0036 (A : Class) : (nb081_alpha_dummy_013 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_013, fv_syn_c0] using (nb081_compact_fv_empty_0010 A)

theorem nb081_wpp_notmem_0037 (x : Var) (y : Var) : (nb081_alpha_dummy_015 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_015, fv_syn_c0] using (nb081_compact_fv_empty_0011 x y)

theorem nb081_wpp_notmem_0038 (A : Class) : (nb081_alpha_dummy_005 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_005, fv_syn_c0] using (nb081_compact_fv_empty_0012 A)

theorem nb081_wpp_notmem_0039 (x : Var) (y : Var) : (nb081_alpha_dummy_007 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_007, fv_syn_c0] using (nb081_compact_fv_empty_0013 x y)

theorem nb081_wpp_notmem_0040 (A : Class) : (nb081_alpha_dummy_004 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_004, fv_syn_c0] using (nb081_compact_fv_empty_0014 A)

theorem nb081_wpp_notmem_0041 (x : Var) (y : Var) : (nb081_alpha_dummy_006 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_006, fv_syn_c0] using (nb081_compact_fv_empty_0015 x y)

theorem nb081_wpp_notmem_0042 (A : Class) : (nb081_alpha_dummy_010 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_010, fv_syn_c0] using (nb081_compact_fv_empty_0016 A)

theorem nb081_wpp_notmem_0043 (x : Var) (y : Var) : (nb081_alpha_dummy_011 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_011, fv_syn_c0] using (nb081_compact_fv_empty_0017 x y)

theorem nb081_wpp_notmem_0044 (A : Class) : (nb081_alpha_dummy_008 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_008, fv_syn_c0] using (nb081_compact_fv_empty_0018 A)

theorem nb081_wpp_notmem_0045 (x : Var) (y : Var) : (nb081_alpha_dummy_009 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_009, fv_syn_c0] using (nb081_compact_fv_empty_0019 x y)

theorem nb081_wpp_notmem_0046 (A : Class) : (nb081_alpha_dummy_001 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_001, fv_syn_c0] using (nb081_compact_fv_empty_0020 A)

theorem nb081_wpp_notmem_0047 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb081_compact_fv_empty_0021 y)

theorem nb081_wpp_notmem_0048 (A : Class) : (nb081_alpha_dummy_000 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_000, fv_syn_c0] using (nb081_compact_fv_empty_0022 A)

theorem nb081_wpp_notmem_0049 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb081_compact_fv_empty_0023 x)

theorem nb081_wpp_notmem_0050 (A : Class) : (nb081_alpha_dummy_002 A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_002, fv_syn_c0] using (nb081_compact_fv_empty_0024 A)

theorem nb081_wpp_notmem_0051 (x : Var) (y : Var) (A : Class) : (nb081_alpha_dummy_003 x y A) ∉ ((syn_c0)).fv := by
  simpa only [nb081_alpha_dummy_003, fv_syn_c0] using (nb081_compact_fv_empty_0025 x y A)

theorem nb081_compact_envfresh_0001 (x : Var) (y : Var) (A : Class) : TEnvFresh [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A), (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)), ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A), (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)), ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb081_alpha_dummy_020 A) (nb081_alpha_dummy_023 x y) (nb081_wpp_notmem_0026 A) (nb081_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_019 A) (nb081_alpha_dummy_022 x y) (nb081_wpp_notmem_0028 A) (nb081_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_018 A) (nb081_alpha_dummy_021 x y) (nb081_wpp_notmem_0030 A) (nb081_wpp_notmem_0031 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_016 A) (nb081_alpha_dummy_017 x y) (nb081_wpp_notmem_0032 A) (nb081_wpp_notmem_0033 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_012 A) (nb081_alpha_dummy_014 x y) (nb081_wpp_notmem_0034 A) (nb081_wpp_notmem_0035 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_013 A) (nb081_alpha_dummy_015 x y) (nb081_wpp_notmem_0036 A) (nb081_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_005 A) (nb081_alpha_dummy_007 x y) (nb081_wpp_notmem_0038 A) (nb081_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_004 A) (nb081_alpha_dummy_006 x y) (nb081_wpp_notmem_0040 A) (nb081_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_010 A) (nb081_alpha_dummy_011 x y) (nb081_wpp_notmem_0042 A) (nb081_wpp_notmem_0043 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_008 A) (nb081_alpha_dummy_009 x y) (nb081_wpp_notmem_0044 A) (nb081_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb081_alpha_dummy_001 A) y (nb081_wpp_notmem_0046 A) (nb081_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb081_alpha_dummy_000 A) x (nb081_wpp_notmem_0048 A) (nb081_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb081_alpha_dummy_002 A) (nb081_alpha_dummy_003 x y A) (nb081_wpp_notmem_0050 A) (nb081_wpp_notmem_0051 x y A) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb081_wpp_refl_0001 (x : Var) (y : Var) (A : Class) : TReflOn [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A), (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)), ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A), (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)), ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb081_compact_envfresh_0001 x y A)

theorem nb081_wpp_notmem_0052 (A : Class) : (nb081_alpha_dummy_016 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_016, fv_syn_cnnc] using (nb081_compact_fv_empty_0006 A)

theorem nb081_wpp_notmem_0053 (x : Var) (y : Var) : (nb081_alpha_dummy_017 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_017, fv_syn_cnnc] using (nb081_compact_fv_empty_0007 x y)

theorem nb081_wpp_notmem_0054 (A : Class) : (nb081_alpha_dummy_012 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_012, fv_syn_cnnc] using (nb081_compact_fv_empty_0008 A)

theorem nb081_wpp_notmem_0055 (x : Var) (y : Var) : (nb081_alpha_dummy_014 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_014, fv_syn_cnnc] using (nb081_compact_fv_empty_0009 x y)

theorem nb081_wpp_notmem_0056 (A : Class) : (nb081_alpha_dummy_013 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_013, fv_syn_cnnc] using (nb081_compact_fv_empty_0010 A)

theorem nb081_wpp_notmem_0057 (x : Var) (y : Var) : (nb081_alpha_dummy_015 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_015, fv_syn_cnnc] using (nb081_compact_fv_empty_0011 x y)

theorem nb081_wpp_notmem_0058 (A : Class) : (nb081_alpha_dummy_005 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_005, fv_syn_cnnc] using (nb081_compact_fv_empty_0012 A)

theorem nb081_wpp_notmem_0059 (x : Var) (y : Var) : (nb081_alpha_dummy_007 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_007, fv_syn_cnnc] using (nb081_compact_fv_empty_0013 x y)

theorem nb081_wpp_notmem_0060 (A : Class) : (nb081_alpha_dummy_004 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_004, fv_syn_cnnc] using (nb081_compact_fv_empty_0014 A)

theorem nb081_wpp_notmem_0061 (x : Var) (y : Var) : (nb081_alpha_dummy_006 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_006, fv_syn_cnnc] using (nb081_compact_fv_empty_0015 x y)

theorem nb081_wpp_notmem_0062 (A : Class) : (nb081_alpha_dummy_010 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_010, fv_syn_cnnc] using (nb081_compact_fv_empty_0016 A)

theorem nb081_wpp_notmem_0063 (x : Var) (y : Var) : (nb081_alpha_dummy_011 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_011, fv_syn_cnnc] using (nb081_compact_fv_empty_0017 x y)

theorem nb081_wpp_notmem_0064 (A : Class) : (nb081_alpha_dummy_008 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_008, fv_syn_cnnc] using (nb081_compact_fv_empty_0018 A)

theorem nb081_wpp_notmem_0065 (x : Var) (y : Var) : (nb081_alpha_dummy_009 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_009, fv_syn_cnnc] using (nb081_compact_fv_empty_0019 x y)

theorem nb081_wpp_notmem_0066 (A : Class) : (nb081_alpha_dummy_001 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_001, fv_syn_cnnc] using (nb081_compact_fv_empty_0020 A)

theorem nb081_wpp_notmem_0067 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb081_compact_fv_empty_0021 y)

theorem nb081_wpp_notmem_0068 (A : Class) : (nb081_alpha_dummy_000 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb081_alpha_dummy_000, fv_syn_cnnc] using (nb081_compact_fv_empty_0022 A)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
