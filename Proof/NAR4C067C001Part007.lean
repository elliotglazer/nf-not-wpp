import NAR4C067C001Part006

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

theorem nb067_support_mem_0045 : (nb067_alpha_dummy_002) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0046 (x : Var) (y : Var) (f : Var) : y ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0047 (x : Var) (y : Var) (f : Var) : y ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0048 : (nb067_alpha_dummy_002) ∈ (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0049 (x : Var) (y : Var) (f : Var) : y ∈ (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0050 : (nb067_alpha_dummy_002) ∈ (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0051 : (nb067_alpha_dummy_002) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0052 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0053 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0054 : (nb067_alpha_dummy_002) ∈ (((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0055 (x : Var) (y : Var) : y ∈ (((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0056 : (nb067_alpha_dummy_016) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_016))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0057 (x : Var) (y : Var) : (nb067_alpha_dummy_018 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0058 : (nb067_alpha_dummy_016) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0059 (x : Var) (y : Var) : (nb067_alpha_dummy_018 x y) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0060 : (nb067_alpha_dummy_008) ∈ (((Class.cv (nb067_alpha_dummy_008))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0061 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_010 x y f) ∈ (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0062 : (nb067_alpha_dummy_051) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_051)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_051)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_051))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0063 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_053 x y f) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_053 x y f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0064 : (nb067_alpha_dummy_051) ∈ (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0065 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_053 x y f) ∈ (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0066 : (nb067_alpha_dummy_058) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0067 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_061 x y f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0068 : (nb067_alpha_dummy_058) ∈ (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0069 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_061 x y f) ∈ (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0070 : (nb067_alpha_dummy_059) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0071 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_062 x y f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0072 : (nb067_alpha_dummy_059) ∈ (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0073 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_062 x y f) ∈ (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0074 : (nb067_alpha_dummy_058) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_058)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_059)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0075 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_061 x y f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_061 x y f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0076 : (nb067_alpha_dummy_058) ∈ (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0077 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_061 x y f) ∈ (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_061 x y f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0078 : (nb067_alpha_dummy_059) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_058)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_059)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0079 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_062 x y f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_061 x y f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0080 : (nb067_alpha_dummy_059) ∈ (((Class.cv (nb067_alpha_dummy_059))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0081 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_062 x y f) ∈ (((Class.cv (nb067_alpha_dummy_062 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0082 : (nb067_alpha_dummy_003) ∈ (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0083 : (nb067_alpha_dummy_003) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0084 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_004 x y f) ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0085 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_004 x y f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0086 : (nb067_alpha_dummy_003) ∈ (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0087 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_004 x y f) ∈ (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0088 : (nb067_alpha_dummy_008) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_008))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0089 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_010 x y f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0090 : (nb067_alpha_dummy_008) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0091 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_010 x y f) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0092 : (nb067_alpha_dummy_083) ∈ (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0093 (f : Var) : (nb067_alpha_dummy_086 f) ∈ (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb067_alpha_dummy_088 f))) (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_087 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0094 : (nb067_alpha_dummy_084) ∈ (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0095 (f : Var) : (nb067_alpha_dummy_087 f) ∈ (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb067_alpha_dummy_088 f))) (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_087 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0096 : (nb067_alpha_dummy_083) ∈ (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0097 : (nb067_alpha_dummy_083) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0098 (f : Var) : (nb067_alpha_dummy_086 f) ∈ (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0099 (f : Var) : (nb067_alpha_dummy_086 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0100 : (nb067_alpha_dummy_083) ∈ (((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0101 (f : Var) : (nb067_alpha_dummy_086 f) ∈ (((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0102 : (nb067_alpha_dummy_092) ∈ (((Class.cv (nb067_alpha_dummy_092))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0103 (f : Var) : (nb067_alpha_dummy_094 f) ∈ (((Class.cv (nb067_alpha_dummy_094 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0104 : (nb067_alpha_dummy_099) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_099))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0105 (f : Var) : (nb067_alpha_dummy_101 f) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_101 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0106 : (nb067_alpha_dummy_099) ∈ (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0107 (f : Var) : (nb067_alpha_dummy_101 f) ∈ (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0108 : (nb067_alpha_dummy_106) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0109 (f : Var) : (nb067_alpha_dummy_109 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0110 : (nb067_alpha_dummy_106) ∈ (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0111 (f : Var) : (nb067_alpha_dummy_109 f) ∈ (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0112 : (nb067_alpha_dummy_107) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0113 (f : Var) : (nb067_alpha_dummy_110 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0114 : (nb067_alpha_dummy_107) ∈ (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0115 (f : Var) : (nb067_alpha_dummy_110 f) ∈ (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0116 : (nb067_alpha_dummy_106) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_106)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_107)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0117 (f : Var) : (nb067_alpha_dummy_109 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_109 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_110 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0118 : (nb067_alpha_dummy_106) ∈ (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_106))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0119 (f : Var) : (nb067_alpha_dummy_109 f) ∈ (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_109 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0120 : (nb067_alpha_dummy_107) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_106)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_107)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0121 (f : Var) : (nb067_alpha_dummy_110 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_109 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_110 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0122 : (nb067_alpha_dummy_107) ∈ (((Class.cv (nb067_alpha_dummy_107))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0123 (f : Var) : (nb067_alpha_dummy_110 f) ∈ (((Class.cv (nb067_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0124 : (nb067_alpha_dummy_084) ∈ (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0125 : (nb067_alpha_dummy_084) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0126 (f : Var) : (nb067_alpha_dummy_087 f) ∈ (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0127 (f : Var) : (nb067_alpha_dummy_087 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0128 : (nb067_alpha_dummy_084) ∈ (((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0129 (f : Var) : (nb067_alpha_dummy_087 f) ∈ (((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0130 : (nb067_alpha_dummy_092) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_092))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0131 (f : Var) : (nb067_alpha_dummy_094 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0132 : (nb067_alpha_dummy_092) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0133 (f : Var) : (nb067_alpha_dummy_094 f) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0134 : (nb067_alpha_dummy_083) ∈ (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0135 : (nb067_alpha_dummy_083) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0136 (f : Var) : (nb067_alpha_dummy_086 f) ∈ (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0137 (f : Var) : (nb067_alpha_dummy_086 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0138 : (nb067_alpha_dummy_083) ∈ (((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0139 (f : Var) : (nb067_alpha_dummy_086 f) ∈ (((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0140 : (nb067_alpha_dummy_128) ∈ (((Class.cv (nb067_alpha_dummy_128))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0141 (f : Var) : (nb067_alpha_dummy_130 f) ∈ (((Class.cv (nb067_alpha_dummy_130 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0142 : (nb067_alpha_dummy_135) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_135))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0143 (f : Var) : (nb067_alpha_dummy_137 f) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_137 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0144 : (nb067_alpha_dummy_135) ∈ (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0145 (f : Var) : (nb067_alpha_dummy_137 f) ∈ (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0146 : (nb067_alpha_dummy_142) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0147 (f : Var) : (nb067_alpha_dummy_145 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0148 : (nb067_alpha_dummy_142) ∈ (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0149 (f : Var) : (nb067_alpha_dummy_145 f) ∈ (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0150 : (nb067_alpha_dummy_143) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0151 (f : Var) : (nb067_alpha_dummy_146 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0152 : (nb067_alpha_dummy_143) ∈ (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0153 (f : Var) : (nb067_alpha_dummy_146 f) ∈ (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0154 : (nb067_alpha_dummy_142) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_142)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_143)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0155 (f : Var) : (nb067_alpha_dummy_145 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_145 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_146 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0156 : (nb067_alpha_dummy_142) ∈ (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_142))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0157 (f : Var) : (nb067_alpha_dummy_145 f) ∈ (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_145 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0158 : (nb067_alpha_dummy_143) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_142)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_143)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0159 (f : Var) : (nb067_alpha_dummy_146 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_145 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_146 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0160 : (nb067_alpha_dummy_143) ∈ (((Class.cv (nb067_alpha_dummy_143))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0161 (f : Var) : (nb067_alpha_dummy_146 f) ∈ (((Class.cv (nb067_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0162 : (nb067_alpha_dummy_085) ∈ (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0163 : (nb067_alpha_dummy_085) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0164 (f : Var) : (nb067_alpha_dummy_088 f) ∈ (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0165 (f : Var) : (nb067_alpha_dummy_088 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0166 : (nb067_alpha_dummy_085) ∈ (((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0167 (f : Var) : (nb067_alpha_dummy_088 f) ∈ (((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0168 : (nb067_alpha_dummy_128) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_128))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0169 (f : Var) : (nb067_alpha_dummy_130 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0170 : (nb067_alpha_dummy_128) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0171 (f : Var) : (nb067_alpha_dummy_130 f) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0172 : (nb067_alpha_dummy_163) ∈ (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_163)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0173 (f : Var) : (nb067_alpha_dummy_165 f) ∈ (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_165 f)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0174 : (nb067_alpha_dummy_164) ∈ (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_163)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0175 (f : Var) : (nb067_alpha_dummy_166 f) ∈ (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_165 f)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0176 : (nb067_alpha_dummy_163) ∈ (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0177 : (nb067_alpha_dummy_163) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
