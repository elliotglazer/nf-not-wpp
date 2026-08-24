import NAR4C074C001Part003

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

theorem nb074_support_mem_0075 (x : Var) : (nb074_alpha_dummy_043 x) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_044 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0076 : (nb074_alpha_dummy_041) ∈ (((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_045) (syn_wrex (nb074_alpha_dummy_046) (Class.cv (nb074_alpha_dummy_041)) (Wff.classEq (Class.cv (nb074_alpha_dummy_045)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_046))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0072) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0077 (x : Var) : (nb074_alpha_dummy_043 x) ∈ (((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_047 x) (syn_wrex (nb074_alpha_dummy_048 x) (Class.cv (nb074_alpha_dummy_043 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_047 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0074 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0078 : (nb074_alpha_dummy_046) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_046))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0079 (x : Var) : (nb074_alpha_dummy_048 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_048 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0080 : (nb074_alpha_dummy_046) ∈ (((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_046)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0081 (x : Var) : (nb074_alpha_dummy_048 x) ∈ (((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_048 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0082 : (nb074_alpha_dummy_081) ∈ (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000)) (Class.cv (nb074_alpha_dummy_081)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0083 (x : Var) : (nb074_alpha_dummy_083 x) ∈ (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x) (Class.cv (nb074_alpha_dummy_083 x)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0084 : (nb074_alpha_dummy_082) ∈ (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000)) (Class.cv (nb074_alpha_dummy_081)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0085 (x : Var) : (nb074_alpha_dummy_084 x) ∈ (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x) (Class.cv (nb074_alpha_dummy_083 x)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0086 : (nb074_alpha_dummy_081) ∈ (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0087 : (nb074_alpha_dummy_081) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0088 (x : Var) : (nb074_alpha_dummy_083 x) ∈ (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0089 (x : Var) : (nb074_alpha_dummy_083 x) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0090 : (nb074_alpha_dummy_081) ∈ (((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0086) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0091 (x : Var) : (nb074_alpha_dummy_083 x) ∈ (((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0088 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0092 : (nb074_alpha_dummy_088) ∈ (((Class.cv (nb074_alpha_dummy_088))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0093 (x : Var) : (nb074_alpha_dummy_090 x) ∈ (((Class.cv (nb074_alpha_dummy_090 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0094 : (nb074_alpha_dummy_095) ∈ (((Wff.classMem (Class.cv (nb074_alpha_dummy_095)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_095)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_095))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0095 (x : Var) : (nb074_alpha_dummy_097 x) ∈ (((Wff.classMem (Class.cv (nb074_alpha_dummy_097 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_097 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_097 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0096 : (nb074_alpha_dummy_095) ∈ (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0097 (x : Var) : (nb074_alpha_dummy_097 x) ∈ (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0098 : (nb074_alpha_dummy_102) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0099 (x : Var) : (nb074_alpha_dummy_105 x) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0100 : (nb074_alpha_dummy_102) ∈ (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0101 (x : Var) : (nb074_alpha_dummy_105 x) ∈ (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0102 : (nb074_alpha_dummy_103) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_102)) (Class.cv (nb074_alpha_dummy_103)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0103 (x : Var) : (nb074_alpha_dummy_106 x) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_105 x)) (Class.cv (nb074_alpha_dummy_106 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0104 : (nb074_alpha_dummy_103) ∈ (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0105 (x : Var) : (nb074_alpha_dummy_106 x) ∈ (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0106 : (nb074_alpha_dummy_102) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_102)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_103)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0107 (x : Var) : (nb074_alpha_dummy_105 x) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_105 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_106 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0108 : (nb074_alpha_dummy_102) ∈ (((Class.cv (nb074_alpha_dummy_102))).fv ∪ ((Class.cv (nb074_alpha_dummy_102))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0109 (x : Var) : (nb074_alpha_dummy_105 x) ∈ (((Class.cv (nb074_alpha_dummy_105 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_105 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0110 : (nb074_alpha_dummy_103) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_102)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_103)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0111 (x : Var) : (nb074_alpha_dummy_106 x) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_105 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_106 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0112 : (nb074_alpha_dummy_103) ∈ (((Class.cv (nb074_alpha_dummy_103))).fv ∪ ((Class.cv (nb074_alpha_dummy_103))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0113 (x : Var) : (nb074_alpha_dummy_106 x) ∈ (((Class.cv (nb074_alpha_dummy_106 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_106 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0114 : (nb074_alpha_dummy_082) ∈ (((Class.cv (nb074_alpha_dummy_081))).fv ∪ ((Class.cv (nb074_alpha_dummy_082))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0115 : (nb074_alpha_dummy_082) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cphi (Class.cv (nb074_alpha_dummy_088)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0116 (x : Var) : (nb074_alpha_dummy_084 x) ∈ (((Class.cv (nb074_alpha_dummy_083 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_084 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0117 (x : Var) : (nb074_alpha_dummy_084 x) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0118 : (nb074_alpha_dummy_082) ∈ (((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_087) (syn_wrex (nb074_alpha_dummy_088) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_087)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_088))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0114) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0119 (x : Var) : (nb074_alpha_dummy_084 x) ∈ (((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_089 x) (syn_wrex (nb074_alpha_dummy_090 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_089 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0116 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0120 : (nb074_alpha_dummy_088) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_088))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0121 (x : Var) : (nb074_alpha_dummy_090 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0122 : (nb074_alpha_dummy_088) ∈ (((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_088)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0123 (x : Var) : (nb074_alpha_dummy_090 x) ∈ (((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_090 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0124 : (nb074_alpha_dummy_082) ∈ (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0125 : (nb074_alpha_dummy_082) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0126 (x : Var) : (nb074_alpha_dummy_084 x) ∈ (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0127 (x : Var) : (nb074_alpha_dummy_084 x) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0128 : (nb074_alpha_dummy_082) ∈ (((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0129 (x : Var) : (nb074_alpha_dummy_084 x) ∈ (((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0130 : (nb074_alpha_dummy_124) ∈ (((Class.cv (nb074_alpha_dummy_124))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0131 (x : Var) : (nb074_alpha_dummy_126 x) ∈ (((Class.cv (nb074_alpha_dummy_126 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0132 : (nb074_alpha_dummy_131) ∈ (((Wff.classMem (Class.cv (nb074_alpha_dummy_131)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_131)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_131))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0133 (x : Var) : (nb074_alpha_dummy_133 x) ∈ (((Wff.classMem (Class.cv (nb074_alpha_dummy_133 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb074_alpha_dummy_133 x)) (syn_c1c))).fv ∪ ((Class.cv (nb074_alpha_dummy_133 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0134 : (nb074_alpha_dummy_131) ∈ (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0135 (x : Var) : (nb074_alpha_dummy_133 x) ∈ (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0136 : (nb074_alpha_dummy_138) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0137 (x : Var) : (nb074_alpha_dummy_141 x) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0138 : (nb074_alpha_dummy_138) ∈ (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0139 (x : Var) : (nb074_alpha_dummy_141 x) ∈ (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0140 : (nb074_alpha_dummy_139) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_138)) (Class.cv (nb074_alpha_dummy_139)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0141 (x : Var) : (nb074_alpha_dummy_142 x) ∈ (((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv ∪ ((syn_cnin (Class.cv (nb074_alpha_dummy_141 x)) (Class.cv (nb074_alpha_dummy_142 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0142 : (nb074_alpha_dummy_139) ∈ (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0143 (x : Var) : (nb074_alpha_dummy_142 x) ∈ (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0144 : (nb074_alpha_dummy_138) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_138)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_139)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0145 (x : Var) : (nb074_alpha_dummy_141 x) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_141 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_142 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0146 : (nb074_alpha_dummy_138) ∈ (((Class.cv (nb074_alpha_dummy_138))).fv ∪ ((Class.cv (nb074_alpha_dummy_138))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0147 (x : Var) : (nb074_alpha_dummy_141 x) ∈ (((Class.cv (nb074_alpha_dummy_141 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_141 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0148 : (nb074_alpha_dummy_139) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_138)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_139)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0149 (x : Var) : (nb074_alpha_dummy_142 x) ∈ (((syn_ccompl (Class.cv (nb074_alpha_dummy_141 x)))).fv ∪ ((syn_ccompl (Class.cv (nb074_alpha_dummy_142 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0150 : (nb074_alpha_dummy_139) ∈ (((Class.cv (nb074_alpha_dummy_139))).fv ∪ ((Class.cv (nb074_alpha_dummy_139))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0151 (x : Var) : (nb074_alpha_dummy_142 x) ∈ (((Class.cv (nb074_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_142 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0152 : (nb074_alpha_dummy_081) ∈ (((Class.cv (nb074_alpha_dummy_082))).fv ∪ ((Class.cv (nb074_alpha_dummy_081))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0153 : (nb074_alpha_dummy_081) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0154 (x : Var) : (nb074_alpha_dummy_083 x) ∈ (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪ ((Class.cv (nb074_alpha_dummy_083 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0155 (x : Var) : (nb074_alpha_dummy_083 x) ∈ (((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0156 : (nb074_alpha_dummy_081) ∈ (((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_123) (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_081)) (Wff.classEq (Class.cv (nb074_alpha_dummy_123)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_124))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0152) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0157 (x : Var) : (nb074_alpha_dummy_083 x) ∈ (((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb074_alpha_dummy_125 x) (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_083 x)) (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x)) (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0154 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb074_support_mem_0158 : (nb074_alpha_dummy_124) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_124))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0159 (x : Var) : (nb074_alpha_dummy_126 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0160 : (nb074_alpha_dummy_124) ∈ (((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_124)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0161 (x : Var) : (nb074_alpha_dummy_126 x) ∈ (((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv ∪ ((syn_cphi (Class.cv (nb074_alpha_dummy_126 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0162 : (nb074_alpha_dummy_000) ∈ (((syn_ccnv (Class.cv (nb074_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0163 (x : Var) : x ∈ (((syn_ccnv (Class.cv x))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0164 : (nb074_alpha_dummy_000) ∈ (({(nb074_alpha_dummy_081)} : Finset Var) ∪ ({(nb074_alpha_dummy_082)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_082)) (Class.cv (nb074_alpha_dummy_000)) (Class.cv (nb074_alpha_dummy_081)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0165 (x : Var) : x ∈ (({(nb074_alpha_dummy_083 x)} : Finset Var) ∪ ({(nb074_alpha_dummy_084 x)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb074_alpha_dummy_084 x)) (Class.cv x) (Class.cv (nb074_alpha_dummy_083 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0166 : (nb074_alpha_dummy_000) ∈ (((Class.cv (nb074_alpha_dummy_000))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_support_mem_0167 (x : Var) : x ∈ (((Class.cv x)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb074_compact_fv_empty_0000 : (nb074_alpha_dummy_021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0000 : (nb074_alpha_dummy_021) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_021, fv_syn_c1c] using (nb074_compact_fv_empty_0000)

theorem nb074_compact_fv_empty_0001 (x : Var) : (nb074_alpha_dummy_024 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0001 (x : Var) : (nb074_alpha_dummy_024 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_024, fv_syn_c1c] using (nb074_compact_fv_empty_0001 x)

theorem nb074_compact_fv_empty_0002 : (nb074_alpha_dummy_020) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0002 : (nb074_alpha_dummy_020) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_020, fv_syn_c1c] using (nb074_compact_fv_empty_0002)

theorem nb074_compact_fv_empty_0003 (x : Var) : (nb074_alpha_dummy_023 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0003 (x : Var) : (nb074_alpha_dummy_023 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_023, fv_syn_c1c] using (nb074_compact_fv_empty_0003 x)

theorem nb074_compact_fv_empty_0004 : (nb074_alpha_dummy_019) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0004 : (nb074_alpha_dummy_019) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_019, fv_syn_c1c] using (nb074_compact_fv_empty_0004)

theorem nb074_compact_fv_empty_0005 (x : Var) : (nb074_alpha_dummy_022 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0005 (x : Var) : (nb074_alpha_dummy_022 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_022, fv_syn_c1c] using (nb074_compact_fv_empty_0005 x)

theorem nb074_compact_fv_empty_0006 : (nb074_alpha_dummy_017) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0006 : (nb074_alpha_dummy_017) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_017, fv_syn_c1c] using (nb074_compact_fv_empty_0006)

theorem nb074_compact_fv_empty_0007 (x : Var) : (nb074_alpha_dummy_018 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0007 (x : Var) : (nb074_alpha_dummy_018 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_018, fv_syn_c1c] using (nb074_compact_fv_empty_0007 x)

theorem nb074_compact_fv_empty_0008 : (nb074_alpha_dummy_013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0008 : (nb074_alpha_dummy_013) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_013, fv_syn_c1c] using (nb074_compact_fv_empty_0008)

theorem nb074_compact_fv_empty_0009 (x : Var) : (nb074_alpha_dummy_015 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0009 (x : Var) : (nb074_alpha_dummy_015 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_015, fv_syn_c1c] using (nb074_compact_fv_empty_0009 x)

theorem nb074_compact_fv_empty_0010 : (nb074_alpha_dummy_014) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0010 : (nb074_alpha_dummy_014) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_014, fv_syn_c1c] using (nb074_compact_fv_empty_0010)

theorem nb074_compact_fv_empty_0011 (x : Var) : (nb074_alpha_dummy_016 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0011 (x : Var) : (nb074_alpha_dummy_016 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_016, fv_syn_c1c] using (nb074_compact_fv_empty_0011 x)

theorem nb074_compact_fv_empty_0012 : (nb074_alpha_dummy_006) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0012 : (nb074_alpha_dummy_006) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_006, fv_syn_c1c] using (nb074_compact_fv_empty_0012)

theorem nb074_compact_fv_empty_0013 (x : Var) : (nb074_alpha_dummy_008 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0013 (x : Var) : (nb074_alpha_dummy_008 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_008, fv_syn_c1c] using (nb074_compact_fv_empty_0013 x)

theorem nb074_compact_fv_empty_0014 : (nb074_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0014 : (nb074_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_005, fv_syn_c1c] using (nb074_compact_fv_empty_0014)

theorem nb074_compact_fv_empty_0015 (x : Var) : (nb074_alpha_dummy_007 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0015 (x : Var) : (nb074_alpha_dummy_007 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_007, fv_syn_c1c] using (nb074_compact_fv_empty_0015 x)

theorem nb074_compact_fv_empty_0016 : (nb074_alpha_dummy_011) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0016 : (nb074_alpha_dummy_011) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_011, fv_syn_c1c] using (nb074_compact_fv_empty_0016)

theorem nb074_compact_fv_empty_0017 (x : Var) : (nb074_alpha_dummy_012 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0017 (x : Var) : (nb074_alpha_dummy_012 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_012, fv_syn_c1c] using (nb074_compact_fv_empty_0017 x)

theorem nb074_compact_fv_empty_0018 : (nb074_alpha_dummy_009) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0018 : (nb074_alpha_dummy_009) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_009, fv_syn_c1c] using (nb074_compact_fv_empty_0018)

theorem nb074_compact_fv_empty_0019 (x : Var) : (nb074_alpha_dummy_010 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0019 (x : Var) : (nb074_alpha_dummy_010 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_010, fv_syn_c1c] using (nb074_compact_fv_empty_0019 x)

theorem nb074_compact_fv_empty_0020 : (nb074_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0020 : (nb074_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_001, fv_syn_c1c] using (nb074_compact_fv_empty_0020)

theorem nb074_compact_fv_empty_0021 (x : Var) : (nb074_alpha_dummy_002 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0021 (x : Var) : (nb074_alpha_dummy_002 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_002, fv_syn_c1c] using (nb074_compact_fv_empty_0021 x)

theorem nb074_compact_fv_empty_0022 : (nb074_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0022 : (nb074_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_000, fv_syn_c1c] using (nb074_compact_fv_empty_0022)

theorem nb074_compact_fv_empty_0023 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0023 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb074_compact_fv_empty_0023 x)

theorem nb074_compact_fv_empty_0024 : (nb074_alpha_dummy_003) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0024 : (nb074_alpha_dummy_003) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_003, fv_syn_c1c] using (nb074_compact_fv_empty_0024)

theorem nb074_compact_fv_empty_0025 (x : Var) : (nb074_alpha_dummy_004 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb074_wpp_notmem_0025 (x : Var) : (nb074_alpha_dummy_004 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb074_alpha_dummy_004, fv_syn_c1c] using (nb074_compact_fv_empty_0025 x)

theorem nb074_compact_envfresh_0000 (x : Var) : TEnvFresh [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb074_alpha_dummy_021) (nb074_alpha_dummy_024 x) (nb074_wpp_notmem_0000) (nb074_wpp_notmem_0001 x) (TEnvFresh.consFresh (nb074_alpha_dummy_020) (nb074_alpha_dummy_023 x) (nb074_wpp_notmem_0002) (nb074_wpp_notmem_0003 x) (TEnvFresh.consFresh (nb074_alpha_dummy_019) (nb074_alpha_dummy_022 x) (nb074_wpp_notmem_0004) (nb074_wpp_notmem_0005 x) (TEnvFresh.consFresh (nb074_alpha_dummy_017) (nb074_alpha_dummy_018 x) (nb074_wpp_notmem_0006) (nb074_wpp_notmem_0007 x) (TEnvFresh.consFresh (nb074_alpha_dummy_013) (nb074_alpha_dummy_015 x) (nb074_wpp_notmem_0008) (nb074_wpp_notmem_0009 x) (TEnvFresh.consFresh (nb074_alpha_dummy_014) (nb074_alpha_dummy_016 x) (nb074_wpp_notmem_0010) (nb074_wpp_notmem_0011 x) (TEnvFresh.consFresh (nb074_alpha_dummy_006) (nb074_alpha_dummy_008 x) (nb074_wpp_notmem_0012) (nb074_wpp_notmem_0013 x) (TEnvFresh.consFresh (nb074_alpha_dummy_005) (nb074_alpha_dummy_007 x) (nb074_wpp_notmem_0014) (nb074_wpp_notmem_0015 x) (TEnvFresh.consFresh (nb074_alpha_dummy_011) (nb074_alpha_dummy_012 x) (nb074_wpp_notmem_0016) (nb074_wpp_notmem_0017 x) (TEnvFresh.consFresh (nb074_alpha_dummy_009) (nb074_alpha_dummy_010 x) (nb074_wpp_notmem_0018) (nb074_wpp_notmem_0019 x) (TEnvFresh.consFresh (nb074_alpha_dummy_001) (nb074_alpha_dummy_002 x) (nb074_wpp_notmem_0020) (nb074_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb074_alpha_dummy_000) x (nb074_wpp_notmem_0022) (nb074_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb074_alpha_dummy_003) (nb074_alpha_dummy_004 x) (nb074_wpp_notmem_0024) (nb074_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb074_wpp_refl_0000 (x : Var) : TReflOn [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020), (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)), ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013), (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb074_compact_envfresh_0000 x)

theorem nb074_wpp_notmem_0026 : (nb074_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_021, fv_syn_c0] using (nb074_compact_fv_empty_0000)

theorem nb074_wpp_notmem_0027 (x : Var) : (nb074_alpha_dummy_024 x) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_024, fv_syn_c0] using (nb074_compact_fv_empty_0001 x)

theorem nb074_wpp_notmem_0028 : (nb074_alpha_dummy_020) ∉ ((syn_c0)).fv := by
  simpa only [nb074_alpha_dummy_020, fv_syn_c0] using (nb074_compact_fv_empty_0002)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
