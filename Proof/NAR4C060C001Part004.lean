import NAR4C060C001Part003

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

theorem nb060_support_mem_0085 (y : Var) (z : Var) : y ∈ (((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0086 : (nb060_alpha_dummy_080) ∈ (((Class.cv (nb060_alpha_dummy_080))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0087 (y : Var) (z : Var) : (nb060_alpha_dummy_082 y z) ∈ (((Class.cv (nb060_alpha_dummy_082 y z))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0088 : (nb060_alpha_dummy_087) ∈ (((Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_087)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_087))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0089 (y : Var) (z : Var) : (nb060_alpha_dummy_089 y z) ∈ (((Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_089 y z)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_089 y z))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0090 : (nb060_alpha_dummy_087) ∈ (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0091 (y : Var) (z : Var) : (nb060_alpha_dummy_089 y z) ∈ (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0092 : (nb060_alpha_dummy_094) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0093 (y : Var) (z : Var) : (nb060_alpha_dummy_097 y z) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0094 : (nb060_alpha_dummy_094) ∈ (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0095 (y : Var) (z : Var) : (nb060_alpha_dummy_097 y z) ∈ (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_098 y z))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0096 : (nb060_alpha_dummy_095) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0097 (y : Var) (z : Var) : (nb060_alpha_dummy_098 y z) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0098 : (nb060_alpha_dummy_095) ∈ (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0099 (y : Var) (z : Var) : (nb060_alpha_dummy_098 y z) ∈ (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_098 y z))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0100 : (nb060_alpha_dummy_094) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_094)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_095)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0101 (y : Var) (z : Var) : (nb060_alpha_dummy_097 y z) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_097 y z)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_098 y z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0102 : (nb060_alpha_dummy_094) ∈ (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_094))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0103 (y : Var) (z : Var) : (nb060_alpha_dummy_097 y z) ∈ (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_097 y z))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0104 : (nb060_alpha_dummy_095) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_094)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_095)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0105 (y : Var) (z : Var) : (nb060_alpha_dummy_098 y z) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_097 y z)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_098 y z)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0106 : (nb060_alpha_dummy_095) ∈ (((Class.cv (nb060_alpha_dummy_095))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0107 (y : Var) (z : Var) : (nb060_alpha_dummy_098 y z) ∈ (((Class.cv (nb060_alpha_dummy_098 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_098 y z))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0108 : (nb060_alpha_dummy_004) ∈ (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0109 : (nb060_alpha_dummy_004) ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0110 (y : Var) (z : Var) : z ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0111 (y : Var) (z : Var) : z ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0112 : (nb060_alpha_dummy_004) ∈ (((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0113 (y : Var) (z : Var) : z ∈ (((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0114 : (nb060_alpha_dummy_080) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_080))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0115 (y : Var) (z : Var) : (nb060_alpha_dummy_082 y z) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0116 : (nb060_alpha_dummy_080) ∈ (((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_080)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0117 (y : Var) (z : Var) : (nb060_alpha_dummy_082 y z) ∈ (((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0118 : (nb060_alpha_dummy_002) ∈ (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0119 : (nb060_alpha_dummy_002) ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0120 (x : Var) (z : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0121 (x : Var) (z : Var) : x ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0122 : (nb060_alpha_dummy_002) ∈ (((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0123 (x : Var) (z : Var) : x ∈ (((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0124 : (nb060_alpha_dummy_116) ∈ (((Class.cv (nb060_alpha_dummy_116))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0125 (x : Var) (z : Var) : (nb060_alpha_dummy_118 x z) ∈ (((Class.cv (nb060_alpha_dummy_118 x z))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0126 : (nb060_alpha_dummy_123) ∈ (((Wff.classMem (Class.cv (nb060_alpha_dummy_123)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_123)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_123))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0127 (x : Var) (z : Var) : (nb060_alpha_dummy_125 x z) ∈ (((Wff.classMem (Class.cv (nb060_alpha_dummy_125 x z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_125 x z)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_125 x z))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0128 : (nb060_alpha_dummy_123) ∈ (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0129 (x : Var) (z : Var) : (nb060_alpha_dummy_125 x z) ∈ (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0130 : (nb060_alpha_dummy_130) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0131 (x : Var) (z : Var) : (nb060_alpha_dummy_133 x z) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z)) (Class.cv (nb060_alpha_dummy_134 x z)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z)) (Class.cv (nb060_alpha_dummy_134 x z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0132 : (nb060_alpha_dummy_130) ∈ (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0133 (x : Var) (z : Var) : (nb060_alpha_dummy_133 x z) ∈ (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_134 x z))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0134 : (nb060_alpha_dummy_131) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0135 (x : Var) (z : Var) : (nb060_alpha_dummy_134 x z) ∈ (((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z)) (Class.cv (nb060_alpha_dummy_134 x z)))).fv ∪ ((syn_cnin (Class.cv (nb060_alpha_dummy_133 x z)) (Class.cv (nb060_alpha_dummy_134 x z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0136 : (nb060_alpha_dummy_131) ∈ (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0137 (x : Var) (z : Var) : (nb060_alpha_dummy_134 x z) ∈ (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_134 x z))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0138 : (nb060_alpha_dummy_130) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_130)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_131)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0139 (x : Var) (z : Var) : (nb060_alpha_dummy_133 x z) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_133 x z)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_134 x z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0140 : (nb060_alpha_dummy_130) ∈ (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_130))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0141 (x : Var) (z : Var) : (nb060_alpha_dummy_133 x z) ∈ (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_133 x z))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0142 : (nb060_alpha_dummy_131) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_130)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_131)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0143 (x : Var) (z : Var) : (nb060_alpha_dummy_134 x z) ∈ (((syn_ccompl (Class.cv (nb060_alpha_dummy_133 x z)))).fv ∪ ((syn_ccompl (Class.cv (nb060_alpha_dummy_134 x z)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0144 : (nb060_alpha_dummy_131) ∈ (((Class.cv (nb060_alpha_dummy_131))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0145 (x : Var) (z : Var) : (nb060_alpha_dummy_134 x z) ∈ (((Class.cv (nb060_alpha_dummy_134 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_134 x z))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0146 : (nb060_alpha_dummy_004) ∈ (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0147 : (nb060_alpha_dummy_004) ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0148 (x : Var) (z : Var) : z ∈ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0149 (x : Var) (z : Var) : z ∈ (((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0150 : (nb060_alpha_dummy_004) ∈ (((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0151 (x : Var) (z : Var) : z ∈ (((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb060_support_mem_0152 : (nb060_alpha_dummy_116) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_116))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0153 (x : Var) (z : Var) : (nb060_alpha_dummy_118 x z) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0154 : (nb060_alpha_dummy_116) ∈ (((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_116)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_support_mem_0155 (x : Var) (z : Var) : (nb060_alpha_dummy_118 x z) ∈ (((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb060_compact_fv_empty_0000 : (nb060_alpha_dummy_023) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0000 : (nb060_alpha_dummy_023) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_023, fv_syn_c1c] using (nb060_compact_fv_empty_0000)

theorem nb060_compact_fv_empty_0001 (r : Var) (a : Var) : (nb060_alpha_dummy_026 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0001 (r : Var) (a : Var) : (nb060_alpha_dummy_026 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_026, fv_syn_c1c] using (nb060_compact_fv_empty_0001 r a)

theorem nb060_compact_fv_empty_0002 : (nb060_alpha_dummy_022) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0002 : (nb060_alpha_dummy_022) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_022, fv_syn_c1c] using (nb060_compact_fv_empty_0002)

theorem nb060_compact_fv_empty_0003 (r : Var) (a : Var) : (nb060_alpha_dummy_025 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0003 (r : Var) (a : Var) : (nb060_alpha_dummy_025 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_025, fv_syn_c1c] using (nb060_compact_fv_empty_0003 r a)

theorem nb060_compact_fv_empty_0004 : (nb060_alpha_dummy_021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0004 : (nb060_alpha_dummy_021) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_021, fv_syn_c1c] using (nb060_compact_fv_empty_0004)

theorem nb060_compact_fv_empty_0005 (r : Var) (a : Var) : (nb060_alpha_dummy_024 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0005 (r : Var) (a : Var) : (nb060_alpha_dummy_024 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_024, fv_syn_c1c] using (nb060_compact_fv_empty_0005 r a)

theorem nb060_compact_fv_empty_0006 : (nb060_alpha_dummy_019) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0006 : (nb060_alpha_dummy_019) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_019, fv_syn_c1c] using (nb060_compact_fv_empty_0006)

theorem nb060_compact_fv_empty_0007 (r : Var) (a : Var) : (nb060_alpha_dummy_020 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0007 (r : Var) (a : Var) : (nb060_alpha_dummy_020 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_020, fv_syn_c1c] using (nb060_compact_fv_empty_0007 r a)

theorem nb060_compact_fv_empty_0008 : (nb060_alpha_dummy_015) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0008 : (nb060_alpha_dummy_015) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_015, fv_syn_c1c] using (nb060_compact_fv_empty_0008)

theorem nb060_compact_fv_empty_0009 (r : Var) (a : Var) : (nb060_alpha_dummy_017 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0009 (r : Var) (a : Var) : (nb060_alpha_dummy_017 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_017, fv_syn_c1c] using (nb060_compact_fv_empty_0009 r a)

theorem nb060_compact_fv_empty_0010 : (nb060_alpha_dummy_016) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0010 : (nb060_alpha_dummy_016) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_016, fv_syn_c1c] using (nb060_compact_fv_empty_0010)

theorem nb060_compact_fv_empty_0011 (r : Var) (a : Var) : (nb060_alpha_dummy_018 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0011 (r : Var) (a : Var) : (nb060_alpha_dummy_018 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_018, fv_syn_c1c] using (nb060_compact_fv_empty_0011 r a)

theorem nb060_compact_fv_empty_0012 : (nb060_alpha_dummy_008) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0012 : (nb060_alpha_dummy_008) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_008, fv_syn_c1c] using (nb060_compact_fv_empty_0012)

theorem nb060_compact_fv_empty_0013 (r : Var) (a : Var) : (nb060_alpha_dummy_010 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0013 (r : Var) (a : Var) : (nb060_alpha_dummy_010 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_010, fv_syn_c1c] using (nb060_compact_fv_empty_0013 r a)

theorem nb060_compact_fv_empty_0014 : (nb060_alpha_dummy_007) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0014 : (nb060_alpha_dummy_007) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_007, fv_syn_c1c] using (nb060_compact_fv_empty_0014)

theorem nb060_compact_fv_empty_0015 (r : Var) (a : Var) : (nb060_alpha_dummy_009 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0015 (r : Var) (a : Var) : (nb060_alpha_dummy_009 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_009, fv_syn_c1c] using (nb060_compact_fv_empty_0015 r a)

theorem nb060_compact_fv_empty_0016 : (nb060_alpha_dummy_013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0016 : (nb060_alpha_dummy_013) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_013, fv_syn_c1c] using (nb060_compact_fv_empty_0016)

theorem nb060_compact_fv_empty_0017 (r : Var) (a : Var) : (nb060_alpha_dummy_014 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0017 (r : Var) (a : Var) : (nb060_alpha_dummy_014 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_014, fv_syn_c1c] using (nb060_compact_fv_empty_0017 r a)

theorem nb060_compact_fv_empty_0018 : (nb060_alpha_dummy_011) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0018 : (nb060_alpha_dummy_011) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_011, fv_syn_c1c] using (nb060_compact_fv_empty_0018)

theorem nb060_compact_fv_empty_0019 (r : Var) (a : Var) : (nb060_alpha_dummy_012 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0019 (r : Var) (a : Var) : (nb060_alpha_dummy_012 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_012, fv_syn_c1c] using (nb060_compact_fv_empty_0019 r a)

theorem nb060_compact_fv_empty_0020 : (nb060_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0020 : (nb060_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_000, fv_syn_c1c] using (nb060_compact_fv_empty_0020)

theorem nb060_compact_fv_empty_0021 (a : Var) : a ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0021 (a : Var) : a ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb060_compact_fv_empty_0021 a)

theorem nb060_compact_fv_empty_0022 : (nb060_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0022 : (nb060_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_001, fv_syn_c1c] using (nb060_compact_fv_empty_0022)

theorem nb060_compact_fv_empty_0023 (r : Var) : r ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0023 (r : Var) : r ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb060_compact_fv_empty_0023 r)

theorem nb060_compact_fv_empty_0024 : (nb060_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0024 : (nb060_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_005, fv_syn_c1c] using (nb060_compact_fv_empty_0024)

theorem nb060_compact_fv_empty_0025 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : (nb060_alpha_dummy_006 x y z r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0025 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : (nb060_alpha_dummy_006 x y z r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_006, fv_syn_c1c] using (nb060_compact_fv_empty_0025 x y z r a)

theorem nb060_compact_envfresh_0000 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_023), (nb060_alpha_dummy_026 r a)), ((nb060_alpha_dummy_022), (nb060_alpha_dummy_025 r a)), ((nb060_alpha_dummy_021), (nb060_alpha_dummy_024 r a)), ((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)), ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)), ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)), ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)), ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)), ((nb060_alpha_dummy_013), (nb060_alpha_dummy_014 r a)), ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_023) (nb060_alpha_dummy_026 r a) (nb060_wpp_notmem_0000) (nb060_wpp_notmem_0001 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_022) (nb060_alpha_dummy_025 r a) (nb060_wpp_notmem_0002) (nb060_wpp_notmem_0003 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_021) (nb060_alpha_dummy_024 r a) (nb060_wpp_notmem_0004) (nb060_wpp_notmem_0005 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_019) (nb060_alpha_dummy_020 r a) (nb060_wpp_notmem_0006) (nb060_wpp_notmem_0007 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_015) (nb060_alpha_dummy_017 r a) (nb060_wpp_notmem_0008) (nb060_wpp_notmem_0009 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_016) (nb060_alpha_dummy_018 r a) (nb060_wpp_notmem_0010) (nb060_wpp_notmem_0011 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_008) (nb060_alpha_dummy_010 r a) (nb060_wpp_notmem_0012) (nb060_wpp_notmem_0013 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_007) (nb060_alpha_dummy_009 r a) (nb060_wpp_notmem_0014) (nb060_wpp_notmem_0015 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_013) (nb060_alpha_dummy_014 r a) (nb060_wpp_notmem_0016) (nb060_wpp_notmem_0017 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_011) (nb060_alpha_dummy_012 r a) (nb060_wpp_notmem_0018) (nb060_wpp_notmem_0019 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0020) (nb060_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0022) (nb060_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0024) (nb060_wpp_notmem_0025 x y z r a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb060_wpp_refl_0000 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_023), (nb060_alpha_dummy_026 r a)), ((nb060_alpha_dummy_022), (nb060_alpha_dummy_025 r a)), ((nb060_alpha_dummy_021), (nb060_alpha_dummy_024 r a)), ((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)), ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)), ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)), ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)), ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)), ((nb060_alpha_dummy_013), (nb060_alpha_dummy_014 r a)), ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0000 x y z r a)

theorem nb060_wpp_notmem_0026 : (nb060_alpha_dummy_023) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_023, fv_syn_c0] using (nb060_compact_fv_empty_0000)

theorem nb060_wpp_notmem_0027 (r : Var) (a : Var) : (nb060_alpha_dummy_026 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_026, fv_syn_c0] using (nb060_compact_fv_empty_0001 r a)

theorem nb060_wpp_notmem_0028 : (nb060_alpha_dummy_022) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_022, fv_syn_c0] using (nb060_compact_fv_empty_0002)

theorem nb060_wpp_notmem_0029 (r : Var) (a : Var) : (nb060_alpha_dummy_025 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_025, fv_syn_c0] using (nb060_compact_fv_empty_0003 r a)

theorem nb060_wpp_notmem_0030 : (nb060_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_021, fv_syn_c0] using (nb060_compact_fv_empty_0004)

theorem nb060_wpp_notmem_0031 (r : Var) (a : Var) : (nb060_alpha_dummy_024 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_024, fv_syn_c0] using (nb060_compact_fv_empty_0005 r a)

theorem nb060_wpp_notmem_0032 : (nb060_alpha_dummy_019) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_019, fv_syn_c0] using (nb060_compact_fv_empty_0006)

theorem nb060_wpp_notmem_0033 (r : Var) (a : Var) : (nb060_alpha_dummy_020 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_020, fv_syn_c0] using (nb060_compact_fv_empty_0007 r a)

theorem nb060_wpp_notmem_0034 : (nb060_alpha_dummy_015) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_015, fv_syn_c0] using (nb060_compact_fv_empty_0008)

theorem nb060_wpp_notmem_0035 (r : Var) (a : Var) : (nb060_alpha_dummy_017 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_017, fv_syn_c0] using (nb060_compact_fv_empty_0009 r a)

theorem nb060_wpp_notmem_0036 : (nb060_alpha_dummy_016) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_016, fv_syn_c0] using (nb060_compact_fv_empty_0010)

theorem nb060_wpp_notmem_0037 (r : Var) (a : Var) : (nb060_alpha_dummy_018 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_018, fv_syn_c0] using (nb060_compact_fv_empty_0011 r a)

theorem nb060_wpp_notmem_0038 : (nb060_alpha_dummy_008) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_008, fv_syn_c0] using (nb060_compact_fv_empty_0012)

theorem nb060_wpp_notmem_0039 (r : Var) (a : Var) : (nb060_alpha_dummy_010 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_010, fv_syn_c0] using (nb060_compact_fv_empty_0013 r a)

theorem nb060_wpp_notmem_0040 : (nb060_alpha_dummy_007) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_007, fv_syn_c0] using (nb060_compact_fv_empty_0014)

theorem nb060_wpp_notmem_0041 (r : Var) (a : Var) : (nb060_alpha_dummy_009 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_009, fv_syn_c0] using (nb060_compact_fv_empty_0015 r a)

theorem nb060_wpp_notmem_0042 : (nb060_alpha_dummy_013) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_013, fv_syn_c0] using (nb060_compact_fv_empty_0016)

theorem nb060_wpp_notmem_0043 (r : Var) (a : Var) : (nb060_alpha_dummy_014 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_014, fv_syn_c0] using (nb060_compact_fv_empty_0017 r a)

theorem nb060_wpp_notmem_0044 : (nb060_alpha_dummy_011) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_011, fv_syn_c0] using (nb060_compact_fv_empty_0018)

theorem nb060_wpp_notmem_0045 (r : Var) (a : Var) : (nb060_alpha_dummy_012 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_012, fv_syn_c0] using (nb060_compact_fv_empty_0019 r a)

theorem nb060_wpp_notmem_0046 : (nb060_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_000, fv_syn_c0] using (nb060_compact_fv_empty_0020)

theorem nb060_wpp_notmem_0047 (a : Var) : a ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb060_compact_fv_empty_0021 a)

theorem nb060_wpp_notmem_0048 : (nb060_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_001, fv_syn_c0] using (nb060_compact_fv_empty_0022)

theorem nb060_wpp_notmem_0049 (r : Var) : r ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb060_compact_fv_empty_0023 r)

theorem nb060_wpp_notmem_0050 : (nb060_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_005, fv_syn_c0] using (nb060_compact_fv_empty_0024)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
