import NAR4C090C001Part015

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

theorem nb090_support_mem_0079 (h : Var) : (nb090_alpha_dummy_053 h) ∈ (((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0080 (A : Class) : (nb090_alpha_dummy_058 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0081 (h : Var) : (nb090_alpha_dummy_060 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0082 (A : Class) : (nb090_alpha_dummy_058 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0083 (h : Var) : (nb090_alpha_dummy_060 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0084 (A : Class) : (nb090_alpha_dummy_049 A) ∈ (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0085 (A : Class) : (nb090_alpha_dummy_049 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0086 (h : Var) : (nb090_alpha_dummy_052 h) ∈ (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0087 (h : Var) : (nb090_alpha_dummy_052 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0088 (A : Class) : (nb090_alpha_dummy_049 A) ∈ (((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0089 (h : Var) : (nb090_alpha_dummy_052 h) ∈ (((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0090 (A : Class) : (nb090_alpha_dummy_094 A) ∈ (((Class.cv (nb090_alpha_dummy_094 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0091 (h : Var) : (nb090_alpha_dummy_096 h) ∈ (((Class.cv (nb090_alpha_dummy_096 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0092 (A : Class) : (nb090_alpha_dummy_101 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_101 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_101 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_101 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0093 (h : Var) : (nb090_alpha_dummy_103 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_103 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_103 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_103 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0094 (A : Class) : (nb090_alpha_dummy_101 A) ∈ (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0095 (h : Var) : (nb090_alpha_dummy_103 h) ∈ (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0096 (A : Class) : (nb090_alpha_dummy_108 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0097 (h : Var) : (nb090_alpha_dummy_111 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0098 (A : Class) : (nb090_alpha_dummy_108 A) ∈ (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0099 (h : Var) : (nb090_alpha_dummy_111 h) ∈ (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0100 (A : Class) : (nb090_alpha_dummy_109 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0101 (h : Var) : (nb090_alpha_dummy_112 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0102 (A : Class) : (nb090_alpha_dummy_109 A) ∈ (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0103 (h : Var) : (nb090_alpha_dummy_112 h) ∈ (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0104 (A : Class) : (nb090_alpha_dummy_108 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_108 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_109 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0105 (h : Var) : (nb090_alpha_dummy_111 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_111 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_112 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0106 (A : Class) : (nb090_alpha_dummy_108 A) ∈ (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_108 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0107 (h : Var) : (nb090_alpha_dummy_111 h) ∈ (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_111 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0108 (A : Class) : (nb090_alpha_dummy_109 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_108 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_109 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0109 (h : Var) : (nb090_alpha_dummy_112 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_111 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_112 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0110 (A : Class) : (nb090_alpha_dummy_109 A) ∈ (((Class.cv (nb090_alpha_dummy_109 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0111 (h : Var) : (nb090_alpha_dummy_112 h) ∈ (((Class.cv (nb090_alpha_dummy_112 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0112 (A : Class) : (nb090_alpha_dummy_051 A) ∈ (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0113 (A : Class) : (nb090_alpha_dummy_051 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0114 (h : Var) : (nb090_alpha_dummy_054 h) ∈ (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0115 (h : Var) : (nb090_alpha_dummy_054 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0116 (A : Class) : (nb090_alpha_dummy_051 A) ∈ (((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0117 (h : Var) : (nb090_alpha_dummy_054 h) ∈ (((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0118 (A : Class) : (nb090_alpha_dummy_094 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0119 (h : Var) : (nb090_alpha_dummy_096 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0120 (A : Class) : (nb090_alpha_dummy_094 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0121 (h : Var) : (nb090_alpha_dummy_096 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0122 (A : Class) : (nb090_alpha_dummy_129 A) ∈ (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_129 A)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0123 (h : Var) : (nb090_alpha_dummy_131 h) ∈ (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_131 h)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0124 (A : Class) : (nb090_alpha_dummy_130 A) ∈ (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_129 A)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0125 (h : Var) : (nb090_alpha_dummy_132 h) ∈ (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_131 h)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0126 (A : Class) : (nb090_alpha_dummy_129 A) ∈ (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0127 (A : Class) : (nb090_alpha_dummy_129 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0128 (h : Var) : (nb090_alpha_dummy_131 h) ∈ (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0129 (h : Var) : (nb090_alpha_dummy_131 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0130 (A : Class) : (nb090_alpha_dummy_129 A) ∈ (((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0131 (h : Var) : (nb090_alpha_dummy_131 h) ∈ (((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0132 (A : Class) : (nb090_alpha_dummy_136 A) ∈ (((Class.cv (nb090_alpha_dummy_136 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0133 (h : Var) : (nb090_alpha_dummy_138 h) ∈ (((Class.cv (nb090_alpha_dummy_138 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0134 (A : Class) : (nb090_alpha_dummy_143 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_143 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_143 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_143 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0135 (h : Var) : (nb090_alpha_dummy_145 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_145 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_145 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_145 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0136 (A : Class) : (nb090_alpha_dummy_143 A) ∈ (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0137 (h : Var) : (nb090_alpha_dummy_145 h) ∈ (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0138 (A : Class) : (nb090_alpha_dummy_150 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0139 (h : Var) : (nb090_alpha_dummy_153 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0140 (A : Class) : (nb090_alpha_dummy_150 A) ∈ (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0141 (h : Var) : (nb090_alpha_dummy_153 h) ∈ (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0142 (A : Class) : (nb090_alpha_dummy_151 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0143 (h : Var) : (nb090_alpha_dummy_154 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0144 (A : Class) : (nb090_alpha_dummy_151 A) ∈ (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0145 (h : Var) : (nb090_alpha_dummy_154 h) ∈ (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0146 (A : Class) : (nb090_alpha_dummy_150 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_150 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_151 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0147 (h : Var) : (nb090_alpha_dummy_153 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_153 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_154 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0148 (A : Class) : (nb090_alpha_dummy_150 A) ∈ (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_150 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0149 (h : Var) : (nb090_alpha_dummy_153 h) ∈ (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_153 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0150 (A : Class) : (nb090_alpha_dummy_151 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_150 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_151 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0151 (h : Var) : (nb090_alpha_dummy_154 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_153 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_154 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0152 (A : Class) : (nb090_alpha_dummy_151 A) ∈ (((Class.cv (nb090_alpha_dummy_151 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0153 (h : Var) : (nb090_alpha_dummy_154 h) ∈ (((Class.cv (nb090_alpha_dummy_154 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0154 (A : Class) : (nb090_alpha_dummy_130 A) ∈ (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0155 (A : Class) : (nb090_alpha_dummy_130 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0156 (h : Var) : (nb090_alpha_dummy_132 h) ∈ (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0157 (h : Var) : (nb090_alpha_dummy_132 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0158 (A : Class) : (nb090_alpha_dummy_130 A) ∈ (((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0159 (h : Var) : (nb090_alpha_dummy_132 h) ∈ (((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0160 (A : Class) : (nb090_alpha_dummy_136 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0161 (h : Var) : (nb090_alpha_dummy_138 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0162 (A : Class) : (nb090_alpha_dummy_136 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0163 (h : Var) : (nb090_alpha_dummy_138 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0164 (A : Class) : (nb090_alpha_dummy_130 A) ∈ (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0165 (A : Class) : (nb090_alpha_dummy_130 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0166 (h : Var) : (nb090_alpha_dummy_132 h) ∈ (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0167 (h : Var) : (nb090_alpha_dummy_132 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0168 (A : Class) : (nb090_alpha_dummy_130 A) ∈ (((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0169 (h : Var) : (nb090_alpha_dummy_132 h) ∈ (((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0170 (A : Class) : (nb090_alpha_dummy_172 A) ∈ (((Class.cv (nb090_alpha_dummy_172 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0171 (h : Var) : (nb090_alpha_dummy_174 h) ∈ (((Class.cv (nb090_alpha_dummy_174 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0172 (A : Class) : (nb090_alpha_dummy_179 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_179 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_179 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_179 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0173 (h : Var) : (nb090_alpha_dummy_181 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_181 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_181 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_181 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0174 (A : Class) : (nb090_alpha_dummy_179 A) ∈ (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0175 (h : Var) : (nb090_alpha_dummy_181 h) ∈ (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0176 (A : Class) : (nb090_alpha_dummy_186 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0177 (h : Var) : (nb090_alpha_dummy_189 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0178 (A : Class) : (nb090_alpha_dummy_186 A) ∈ (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0179 (h : Var) : (nb090_alpha_dummy_189 h) ∈ (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0180 (A : Class) : (nb090_alpha_dummy_187 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0181 (h : Var) : (nb090_alpha_dummy_190 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0182 (A : Class) : (nb090_alpha_dummy_187 A) ∈ (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0183 (h : Var) : (nb090_alpha_dummy_190 h) ∈ (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0184 (A : Class) : (nb090_alpha_dummy_186 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_186 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_187 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0185 (h : Var) : (nb090_alpha_dummy_189 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_189 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_190 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0186 (A : Class) : (nb090_alpha_dummy_186 A) ∈ (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_186 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0187 (h : Var) : (nb090_alpha_dummy_189 h) ∈ (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_189 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0188 (A : Class) : (nb090_alpha_dummy_187 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_186 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_187 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0189 (h : Var) : (nb090_alpha_dummy_190 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_189 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_190 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0190 (A : Class) : (nb090_alpha_dummy_187 A) ∈ (((Class.cv (nb090_alpha_dummy_187 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0191 (h : Var) : (nb090_alpha_dummy_190 h) ∈ (((Class.cv (nb090_alpha_dummy_190 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0192 (A : Class) : (nb090_alpha_dummy_129 A) ∈ (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0193 (A : Class) : (nb090_alpha_dummy_129 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0194 (h : Var) : (nb090_alpha_dummy_131 h) ∈ (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0195 (h : Var) : (nb090_alpha_dummy_131 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0196 (A : Class) : (nb090_alpha_dummy_129 A) ∈ (((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0197 (h : Var) : (nb090_alpha_dummy_131 h) ∈ (((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0198 (A : Class) : (nb090_alpha_dummy_172 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0199 (h : Var) : (nb090_alpha_dummy_174 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0200 (A : Class) : (nb090_alpha_dummy_172 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0201 (h : Var) : (nb090_alpha_dummy_174 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0202 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0203 (h : Var) : h ∈ (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0204 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_ccom (Class.cv (nb090_alpha_dummy_000 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0205 (h : Var) : h ∈ (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0206 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0207 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_049 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_051 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_050 A)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0206 A) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0208 (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0209 (h : Var) : h ∈ (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_054 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_053 h)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0208 h) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0210 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_129 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0211 (h : Var) : h ∈ (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_131 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0212 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0213 (h : Var) : h ∈ (((Class.cv h)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0214 (A : Class) : (nb090_alpha_dummy_051 A) ∈ (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0215 (A : Class) : (nb090_alpha_dummy_051 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0216 (h : Var) : (nb090_alpha_dummy_054 h) ∈ (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
