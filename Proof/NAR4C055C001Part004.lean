import NAR4C055C001Part003

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

theorem nb055_support_mem_0009 : (nb055_alpha_dummy_000) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0010 (x : Var) (y : Var) : x ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0011 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0012 : (nb055_alpha_dummy_000) ∈ (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0013 (x : Var) (y : Var) : x ∈ (((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0014 : (nb055_alpha_dummy_000) ∈ (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0015 : (nb055_alpha_dummy_000) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0016 (x : Var) (y : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0017 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0018 : (nb055_alpha_dummy_000) ∈ (((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0019 (x : Var) (y : Var) : x ∈ (((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0020 : (nb055_alpha_dummy_015) ∈ (((Class.cv (nb055_alpha_dummy_015))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0021 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∈ (((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0022 : (nb055_alpha_dummy_022) ∈ (((Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_022)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_022))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0023 (x : Var) (y : Var) : (nb055_alpha_dummy_024 x y) ∈ (((Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_024 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_024 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0024 : (nb055_alpha_dummy_022) ∈ (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0025 (x : Var) (y : Var) : (nb055_alpha_dummy_024 x y) ∈ (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0026 : (nb055_alpha_dummy_029) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0027 (x : Var) (y : Var) : (nb055_alpha_dummy_032 x y) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y)) (Class.cv (nb055_alpha_dummy_033 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y)) (Class.cv (nb055_alpha_dummy_033 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0028 : (nb055_alpha_dummy_029) ∈ (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0029 (x : Var) (y : Var) : (nb055_alpha_dummy_032 x y) ∈ (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_033 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0030 : (nb055_alpha_dummy_030) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0031 (x : Var) (y : Var) : (nb055_alpha_dummy_033 x y) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y)) (Class.cv (nb055_alpha_dummy_033 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y)) (Class.cv (nb055_alpha_dummy_033 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0032 : (nb055_alpha_dummy_030) ∈ (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0033 (x : Var) (y : Var) : (nb055_alpha_dummy_033 x y) ∈ (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_033 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0034 : (nb055_alpha_dummy_029) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_030)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0035 (x : Var) (y : Var) : (nb055_alpha_dummy_032 x y) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_033 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0036 : (nb055_alpha_dummy_029) ∈ (((Class.cv (nb055_alpha_dummy_029))).fv ∪ ((Class.cv (nb055_alpha_dummy_029))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0037 (x : Var) (y : Var) : (nb055_alpha_dummy_032 x y) ∈ (((Class.cv (nb055_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_032 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0038 : (nb055_alpha_dummy_030) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_030)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0039 (x : Var) (y : Var) : (nb055_alpha_dummy_033 x y) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_033 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0040 : (nb055_alpha_dummy_030) ∈ (((Class.cv (nb055_alpha_dummy_030))).fv ∪ ((Class.cv (nb055_alpha_dummy_030))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0041 (x : Var) (y : Var) : (nb055_alpha_dummy_033 x y) ∈ (((Class.cv (nb055_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_033 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0042 : (nb055_alpha_dummy_001) ∈ (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0043 (x : Var) (y : Var) : y ∈ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_ccom (Class.cv x) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0044 : (nb055_alpha_dummy_001) ∈ (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0045 : (nb055_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0046 (x : Var) (y : Var) : y ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0047 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0048 : (nb055_alpha_dummy_001) ∈ (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0049 (x : Var) (y : Var) : y ∈ (((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0050 : (nb055_alpha_dummy_001) ∈ (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0051 : (nb055_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0052 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0053 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0054 : (nb055_alpha_dummy_001) ∈ (((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0055 (x : Var) (y : Var) : y ∈ (((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0056 : (nb055_alpha_dummy_015) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_015))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0057 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0058 : (nb055_alpha_dummy_015) ∈ (((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0059 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∈ (((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0060 : (nb055_alpha_dummy_007) ∈ (((Class.cv (nb055_alpha_dummy_007))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0061 (x : Var) (y : Var) : (nb055_alpha_dummy_009 x y) ∈ (((Class.cv (nb055_alpha_dummy_009 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0062 : (nb055_alpha_dummy_050) ∈ (((Wff.classMem (Class.cv (nb055_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_050))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0063 (x : Var) (y : Var) : (nb055_alpha_dummy_052 x y) ∈ (((Wff.classMem (Class.cv (nb055_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_052 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0064 : (nb055_alpha_dummy_050) ∈ (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0065 (x : Var) (y : Var) : (nb055_alpha_dummy_052 x y) ∈ (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0066 : (nb055_alpha_dummy_057) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0067 (x : Var) (y : Var) : (nb055_alpha_dummy_060 x y) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0068 : (nb055_alpha_dummy_057) ∈ (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0069 (x : Var) (y : Var) : (nb055_alpha_dummy_060 x y) ∈ (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0070 : (nb055_alpha_dummy_058) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0071 (x : Var) (y : Var) : (nb055_alpha_dummy_061 x y) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0072 : (nb055_alpha_dummy_058) ∈ (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0073 (x : Var) (y : Var) : (nb055_alpha_dummy_061 x y) ∈ (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0074 : (nb055_alpha_dummy_057) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0075 (x : Var) (y : Var) : (nb055_alpha_dummy_060 x y) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0076 : (nb055_alpha_dummy_057) ∈ (((Class.cv (nb055_alpha_dummy_057))).fv ∪ ((Class.cv (nb055_alpha_dummy_057))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0077 (x : Var) (y : Var) : (nb055_alpha_dummy_060 x y) ∈ (((Class.cv (nb055_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_060 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0078 : (nb055_alpha_dummy_058) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0079 (x : Var) (y : Var) : (nb055_alpha_dummy_061 x y) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0080 : (nb055_alpha_dummy_058) ∈ (((Class.cv (nb055_alpha_dummy_058))).fv ∪ ((Class.cv (nb055_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0081 (x : Var) (y : Var) : (nb055_alpha_dummy_061 x y) ∈ (((Class.cv (nb055_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0082 : (nb055_alpha_dummy_002) ∈ (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0083 : (nb055_alpha_dummy_002) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0084 (x : Var) (y : Var) : (nb055_alpha_dummy_003 x y) ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0085 (x : Var) (y : Var) : (nb055_alpha_dummy_003 x y) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0086 : (nb055_alpha_dummy_002) ∈ (((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0087 (x : Var) (y : Var) : (nb055_alpha_dummy_003 x y) ∈ (((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0088 : (nb055_alpha_dummy_007) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0089 (x : Var) (y : Var) : (nb055_alpha_dummy_009 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0090 : (nb055_alpha_dummy_007) ∈ (((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0091 (x : Var) (y : Var) : (nb055_alpha_dummy_009 x y) ∈ (((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0092 : (nb055_alpha_dummy_014) ∈ (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014)) (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078))) (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_015)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0093 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∈ (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y) (Class.cv (nb055_alpha_dummy_079 x y))) (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x) (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0094 : (nb055_alpha_dummy_015) ∈ (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014)) (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078))) (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_015)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0095 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∈ (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y) (Class.cv (nb055_alpha_dummy_079 x y))) (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x) (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0096 : (nb055_alpha_dummy_014) ∈ (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0097 : (nb055_alpha_dummy_014) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0098 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∈ (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0099 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0100 : (nb055_alpha_dummy_014) ∈ (((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0096) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0101 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∈ (((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0098 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0102 : (nb055_alpha_dummy_083) ∈ (((Class.cv (nb055_alpha_dummy_083))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0103 (x : Var) (y : Var) : (nb055_alpha_dummy_085 x y) ∈ (((Class.cv (nb055_alpha_dummy_085 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0104 : (nb055_alpha_dummy_090) ∈ (((Wff.classMem (Class.cv (nb055_alpha_dummy_090)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_090)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_090))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0105 (x : Var) (y : Var) : (nb055_alpha_dummy_092 x y) ∈ (((Wff.classMem (Class.cv (nb055_alpha_dummy_092 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_092 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_092 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0106 : (nb055_alpha_dummy_090) ∈ (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0107 (x : Var) (y : Var) : (nb055_alpha_dummy_092 x y) ∈ (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0108 : (nb055_alpha_dummy_097) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0109 (x : Var) (y : Var) : (nb055_alpha_dummy_100 x y) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y)) (Class.cv (nb055_alpha_dummy_101 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y)) (Class.cv (nb055_alpha_dummy_101 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0110 : (nb055_alpha_dummy_097) ∈ (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0111 (x : Var) (y : Var) : (nb055_alpha_dummy_100 x y) ∈ (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_101 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0112 : (nb055_alpha_dummy_098) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0113 (x : Var) (y : Var) : (nb055_alpha_dummy_101 x y) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y)) (Class.cv (nb055_alpha_dummy_101 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y)) (Class.cv (nb055_alpha_dummy_101 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0114 : (nb055_alpha_dummy_098) ∈ (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0115 (x : Var) (y : Var) : (nb055_alpha_dummy_101 x y) ∈ (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_101 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0116 : (nb055_alpha_dummy_097) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_097)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_098)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0117 (x : Var) (y : Var) : (nb055_alpha_dummy_100 x y) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_100 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_101 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0118 : (nb055_alpha_dummy_097) ∈ (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_097))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0119 (x : Var) (y : Var) : (nb055_alpha_dummy_100 x y) ∈ (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_100 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0120 : (nb055_alpha_dummy_098) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_097)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_098)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0121 (x : Var) (y : Var) : (nb055_alpha_dummy_101 x y) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_100 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_101 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0122 : (nb055_alpha_dummy_098) ∈ (((Class.cv (nb055_alpha_dummy_098))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0123 (x : Var) (y : Var) : (nb055_alpha_dummy_101 x y) ∈ (((Class.cv (nb055_alpha_dummy_101 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_101 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0124 : (nb055_alpha_dummy_015) ∈ (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0125 : (nb055_alpha_dummy_015) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0126 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∈ (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0127 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0128 : (nb055_alpha_dummy_015) ∈ (((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0129 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∈ (((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0130 : (nb055_alpha_dummy_083) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_083))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0131 (x : Var) (y : Var) : (nb055_alpha_dummy_085 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0132 : (nb055_alpha_dummy_083) ∈ (((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0133 (x : Var) (y : Var) : (nb055_alpha_dummy_085 x y) ∈ (((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0134 : (nb055_alpha_dummy_014) ∈ (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0135 : (nb055_alpha_dummy_014) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0134) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0134) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0136 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∈ (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0137 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0136 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0136 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
