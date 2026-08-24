import NAR4C068C001Part009

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

theorem nb068_support_mem_0076 (f : Var) : (nb068_alpha_dummy_049 f) ∈ (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0077 (f : Var) : (nb068_alpha_dummy_049 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0078 : (nb068_alpha_dummy_046) ∈ (((Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0079 (f : Var) : (nb068_alpha_dummy_049 f) ∈ (((Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0080 : (nb068_alpha_dummy_054) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_054))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0081 (f : Var) : (nb068_alpha_dummy_056 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0082 : (nb068_alpha_dummy_054) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0083 (f : Var) : (nb068_alpha_dummy_056 f) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0084 : (nb068_alpha_dummy_045) ∈ (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0085 : (nb068_alpha_dummy_045) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cphi (Class.cv (nb068_alpha_dummy_090)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0086 (f : Var) : (nb068_alpha_dummy_048 f) ∈ (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0087 (f : Var) : (nb068_alpha_dummy_048 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0088 : (nb068_alpha_dummy_045) ∈ (((Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cphi (Class.cv (nb068_alpha_dummy_090))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cphi (Class.cv (nb068_alpha_dummy_090))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0089 (f : Var) : (nb068_alpha_dummy_048 f) ∈ (((Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0090 : (nb068_alpha_dummy_090) ∈ (((Class.cv (nb068_alpha_dummy_090))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0091 (f : Var) : (nb068_alpha_dummy_092 f) ∈ (((Class.cv (nb068_alpha_dummy_092 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0092 : (nb068_alpha_dummy_097) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_097)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_097)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_097))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0093 (f : Var) : (nb068_alpha_dummy_099 f) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_099 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_099 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_099 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0094 : (nb068_alpha_dummy_097) ∈ (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0095 (f : Var) : (nb068_alpha_dummy_099 f) ∈ (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0096 : (nb068_alpha_dummy_104) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0097 (f : Var) : (nb068_alpha_dummy_107 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_107 f)) (Class.cv (nb068_alpha_dummy_108 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_107 f)) (Class.cv (nb068_alpha_dummy_108 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0098 : (nb068_alpha_dummy_104) ∈ (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0099 (f : Var) : (nb068_alpha_dummy_107 f) ∈ (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0100 : (nb068_alpha_dummy_105) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0101 (f : Var) : (nb068_alpha_dummy_108 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_107 f)) (Class.cv (nb068_alpha_dummy_108 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_107 f)) (Class.cv (nb068_alpha_dummy_108 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0102 : (nb068_alpha_dummy_105) ∈ (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0103 (f : Var) : (nb068_alpha_dummy_108 f) ∈ (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0104 : (nb068_alpha_dummy_104) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_104)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_105)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0105 (f : Var) : (nb068_alpha_dummy_107 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_107 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_108 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0106 : (nb068_alpha_dummy_104) ∈ (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_104))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0107 (f : Var) : (nb068_alpha_dummy_107 f) ∈ (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_107 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0108 : (nb068_alpha_dummy_105) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_104)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_105)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0109 (f : Var) : (nb068_alpha_dummy_108 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_107 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_108 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0110 : (nb068_alpha_dummy_105) ∈ (((Class.cv (nb068_alpha_dummy_105))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0111 (f : Var) : (nb068_alpha_dummy_108 f) ∈ (((Class.cv (nb068_alpha_dummy_108 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0112 : (nb068_alpha_dummy_047) ∈ (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0113 : (nb068_alpha_dummy_047) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cphi (Class.cv (nb068_alpha_dummy_090)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0114 (f : Var) : (nb068_alpha_dummy_050 f) ∈ (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0115 (f : Var) : (nb068_alpha_dummy_050 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0116 : (nb068_alpha_dummy_047) ∈ (((Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0117 (f : Var) : (nb068_alpha_dummy_050 f) ∈ (((Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0118 : (nb068_alpha_dummy_090) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_090))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0119 (f : Var) : (nb068_alpha_dummy_092 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0120 : (nb068_alpha_dummy_090) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0121 (f : Var) : (nb068_alpha_dummy_092 f) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0122 : (nb068_alpha_dummy_125) ∈ (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_125)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0123 (f : Var) : (nb068_alpha_dummy_127 f) ∈ (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_127 f)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0124 : (nb068_alpha_dummy_126) ∈ (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_125)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0125 (f : Var) : (nb068_alpha_dummy_128 f) ∈ (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_127 f)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0126 : (nb068_alpha_dummy_125) ∈ (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0127 : (nb068_alpha_dummy_125) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cphi (Class.cv (nb068_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0128 (f : Var) : (nb068_alpha_dummy_127 f) ∈ (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0129 (f : Var) : (nb068_alpha_dummy_127 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0130 : (nb068_alpha_dummy_125) ∈ (((Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cphi (Class.cv (nb068_alpha_dummy_132))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cphi (Class.cv (nb068_alpha_dummy_132))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0131 (f : Var) : (nb068_alpha_dummy_127 f) ∈ (((Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0132 : (nb068_alpha_dummy_132) ∈ (((Class.cv (nb068_alpha_dummy_132))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0133 (f : Var) : (nb068_alpha_dummy_134 f) ∈ (((Class.cv (nb068_alpha_dummy_134 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0134 : (nb068_alpha_dummy_139) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_139))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0135 (f : Var) : (nb068_alpha_dummy_141 f) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_141 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0136 : (nb068_alpha_dummy_139) ∈ (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0137 (f : Var) : (nb068_alpha_dummy_141 f) ∈ (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0138 : (nb068_alpha_dummy_146) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0139 (f : Var) : (nb068_alpha_dummy_149 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0140 : (nb068_alpha_dummy_146) ∈ (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0141 (f : Var) : (nb068_alpha_dummy_149 f) ∈ (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0142 : (nb068_alpha_dummy_147) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0143 (f : Var) : (nb068_alpha_dummy_150 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0144 : (nb068_alpha_dummy_147) ∈ (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0145 (f : Var) : (nb068_alpha_dummy_150 f) ∈ (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0146 : (nb068_alpha_dummy_146) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_146)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_147)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0147 (f : Var) : (nb068_alpha_dummy_149 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_149 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_150 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0148 : (nb068_alpha_dummy_146) ∈ (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_146))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0149 (f : Var) : (nb068_alpha_dummy_149 f) ∈ (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_149 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0150 : (nb068_alpha_dummy_147) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_146)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_147)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0151 (f : Var) : (nb068_alpha_dummy_150 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_149 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_150 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0152 : (nb068_alpha_dummy_147) ∈ (((Class.cv (nb068_alpha_dummy_147))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0153 (f : Var) : (nb068_alpha_dummy_150 f) ∈ (((Class.cv (nb068_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0154 : (nb068_alpha_dummy_126) ∈ (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0155 : (nb068_alpha_dummy_126) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cphi (Class.cv (nb068_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0156 (f : Var) : (nb068_alpha_dummy_128 f) ∈ (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0157 (f : Var) : (nb068_alpha_dummy_128 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0158 : (nb068_alpha_dummy_126) ∈ (((Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0159 (f : Var) : (nb068_alpha_dummy_128 f) ∈ (((Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0160 : (nb068_alpha_dummy_132) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_132))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0161 (f : Var) : (nb068_alpha_dummy_134 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0162 : (nb068_alpha_dummy_132) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0163 (f : Var) : (nb068_alpha_dummy_134 f) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0164 : (nb068_alpha_dummy_126) ∈ (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0165 : (nb068_alpha_dummy_126) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0166 (f : Var) : (nb068_alpha_dummy_128 f) ∈ (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0167 (f : Var) : (nb068_alpha_dummy_128 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0168 : (nb068_alpha_dummy_126) ∈ (((Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cphi (Class.cv (nb068_alpha_dummy_168))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0169 (f : Var) : (nb068_alpha_dummy_128 f) ∈ (((Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0170 : (nb068_alpha_dummy_168) ∈ (((Class.cv (nb068_alpha_dummy_168))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0171 (f : Var) : (nb068_alpha_dummy_170 f) ∈ (((Class.cv (nb068_alpha_dummy_170 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0172 : (nb068_alpha_dummy_175) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_175))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0173 (f : Var) : (nb068_alpha_dummy_177 f) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_177 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0174 : (nb068_alpha_dummy_175) ∈ (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0175 (f : Var) : (nb068_alpha_dummy_177 f) ∈ (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0176 : (nb068_alpha_dummy_182) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0177 (f : Var) : (nb068_alpha_dummy_185 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0178 : (nb068_alpha_dummy_182) ∈ (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0179 (f : Var) : (nb068_alpha_dummy_185 f) ∈ (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0180 : (nb068_alpha_dummy_183) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0181 (f : Var) : (nb068_alpha_dummy_186 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0182 : (nb068_alpha_dummy_183) ∈ (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0183 (f : Var) : (nb068_alpha_dummy_186 f) ∈ (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0184 : (nb068_alpha_dummy_182) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_182)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_183)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0185 (f : Var) : (nb068_alpha_dummy_185 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_185 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_186 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0186 : (nb068_alpha_dummy_182) ∈ (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_182))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0187 (f : Var) : (nb068_alpha_dummy_185 f) ∈ (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_185 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0188 : (nb068_alpha_dummy_183) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_182)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_183)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0189 (f : Var) : (nb068_alpha_dummy_186 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_185 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_186 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0190 : (nb068_alpha_dummy_183) ∈ (((Class.cv (nb068_alpha_dummy_183))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0191 (f : Var) : (nb068_alpha_dummy_186 f) ∈ (((Class.cv (nb068_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0192 : (nb068_alpha_dummy_125) ∈ (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0193 : (nb068_alpha_dummy_125) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0194 (f : Var) : (nb068_alpha_dummy_127 f) ∈ (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0195 (f : Var) : (nb068_alpha_dummy_127 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0196 : (nb068_alpha_dummy_125) ∈ (((Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0197 (f : Var) : (nb068_alpha_dummy_127 f) ∈ (((Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0198 : (nb068_alpha_dummy_168) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_168))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0199 (f : Var) : (nb068_alpha_dummy_170 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0200 : (nb068_alpha_dummy_168) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0201 (f : Var) : (nb068_alpha_dummy_170 f) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0202 : (nb068_alpha_dummy_000) ∈ (((syn_cnin (syn_ccom (Class.cv (nb068_alpha_dummy_000)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb068_alpha_dummy_000)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0203 (f : Var) : f ∈ (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0204 : (nb068_alpha_dummy_000) ∈ (((syn_ccom (Class.cv (nb068_alpha_dummy_000)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0205 (f : Var) : f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0206 : (nb068_alpha_dummy_000) ∈ (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0207 : (nb068_alpha_dummy_000) ∈ (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_047))) (syn_wbr (Class.cv (nb068_alpha_dummy_047)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_046)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb068_support_mem_0208 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0209 (f : Var) : f ∈ (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_050 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_049 f)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb068_support_mem_0210 : (nb068_alpha_dummy_000) ∈ (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_125)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0211 (f : Var) : f ∈ (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_127 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0212 : (nb068_alpha_dummy_000) ∈ (((Class.cv (nb068_alpha_dummy_000))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0213 (f : Var) : f ∈ (((Class.cv f)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0214 : (nb068_alpha_dummy_047) ∈ (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
