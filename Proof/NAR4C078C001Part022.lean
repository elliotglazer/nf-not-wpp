import NAR4C078C001Part021

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

theorem nb078_support_mem_0033 : (nb078_alpha_dummy_010) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0034 (f : Var) : (nb078_alpha_dummy_013 f) ∈ (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0035 (f : Var) : (nb078_alpha_dummy_013 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0036 : (nb078_alpha_dummy_010) ∈ (((Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0037 (f : Var) : (nb078_alpha_dummy_013 f) ∈ (((Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0038 : (nb078_alpha_dummy_018) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_018))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0039 (f : Var) : (nb078_alpha_dummy_020 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0040 : (nb078_alpha_dummy_018) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0041 (f : Var) : (nb078_alpha_dummy_020 f) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0042 : (nb078_alpha_dummy_009) ∈ (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0043 : (nb078_alpha_dummy_009) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0044 (f : Var) : (nb078_alpha_dummy_012 f) ∈ (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0045 (f : Var) : (nb078_alpha_dummy_012 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0046 : (nb078_alpha_dummy_009) ∈ (((Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0047 (f : Var) : (nb078_alpha_dummy_012 f) ∈ (((Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0048 : (nb078_alpha_dummy_054) ∈ (((Class.cv (nb078_alpha_dummy_054))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0049 (f : Var) : (nb078_alpha_dummy_056 f) ∈ (((Class.cv (nb078_alpha_dummy_056 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0050 : (nb078_alpha_dummy_061) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_061)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_061)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_061))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0051 (f : Var) : (nb078_alpha_dummy_063 f) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_063 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_063 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_063 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0052 : (nb078_alpha_dummy_061) ∈ (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0053 (f : Var) : (nb078_alpha_dummy_063 f) ∈ (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0054 : (nb078_alpha_dummy_068) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0055 (f : Var) : (nb078_alpha_dummy_071 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0056 : (nb078_alpha_dummy_068) ∈ (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0057 (f : Var) : (nb078_alpha_dummy_071 f) ∈ (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0058 : (nb078_alpha_dummy_069) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0059 (f : Var) : (nb078_alpha_dummy_072 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0060 : (nb078_alpha_dummy_069) ∈ (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0061 (f : Var) : (nb078_alpha_dummy_072 f) ∈ (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0062 : (nb078_alpha_dummy_068) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_068)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_069)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0063 (f : Var) : (nb078_alpha_dummy_071 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_071 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_072 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0064 : (nb078_alpha_dummy_068) ∈ (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_068))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0065 (f : Var) : (nb078_alpha_dummy_071 f) ∈ (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_071 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0066 : (nb078_alpha_dummy_069) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_068)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_069)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0067 (f : Var) : (nb078_alpha_dummy_072 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_071 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_072 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0068 : (nb078_alpha_dummy_069) ∈ (((Class.cv (nb078_alpha_dummy_069))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0069 (f : Var) : (nb078_alpha_dummy_072 f) ∈ (((Class.cv (nb078_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0070 : (nb078_alpha_dummy_011) ∈ (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0071 : (nb078_alpha_dummy_011) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0072 (f : Var) : (nb078_alpha_dummy_014 f) ∈ (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0073 (f : Var) : (nb078_alpha_dummy_014 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0074 : (nb078_alpha_dummy_011) ∈ (((Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0075 (f : Var) : (nb078_alpha_dummy_014 f) ∈ (((Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0076 : (nb078_alpha_dummy_054) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_054))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0077 (f : Var) : (nb078_alpha_dummy_056 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0078 : (nb078_alpha_dummy_054) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0079 (f : Var) : (nb078_alpha_dummy_056 f) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0080 : (nb078_alpha_dummy_089) ∈ (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_089)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0081 (f : Var) : (nb078_alpha_dummy_091 f) ∈ (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_091 f)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0082 : (nb078_alpha_dummy_090) ∈ (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_089)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0083 (f : Var) : (nb078_alpha_dummy_092 f) ∈ (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_091 f)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0084 : (nb078_alpha_dummy_089) ∈ (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0085 : (nb078_alpha_dummy_089) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0086 (f : Var) : (nb078_alpha_dummy_091 f) ∈ (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0087 (f : Var) : (nb078_alpha_dummy_091 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0088 : (nb078_alpha_dummy_089) ∈ (((Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0089 (f : Var) : (nb078_alpha_dummy_091 f) ∈ (((Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0090 : (nb078_alpha_dummy_096) ∈ (((Class.cv (nb078_alpha_dummy_096))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0091 (f : Var) : (nb078_alpha_dummy_098 f) ∈ (((Class.cv (nb078_alpha_dummy_098 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0092 : (nb078_alpha_dummy_103) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_103)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_103)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_103))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0093 (f : Var) : (nb078_alpha_dummy_105 f) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_105 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_105 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_105 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0094 : (nb078_alpha_dummy_103) ∈ (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0095 (f : Var) : (nb078_alpha_dummy_105 f) ∈ (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0096 : (nb078_alpha_dummy_110) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0097 (f : Var) : (nb078_alpha_dummy_113 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0098 : (nb078_alpha_dummy_110) ∈ (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0099 (f : Var) : (nb078_alpha_dummy_113 f) ∈ (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0100 : (nb078_alpha_dummy_111) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0101 (f : Var) : (nb078_alpha_dummy_114 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0102 : (nb078_alpha_dummy_111) ∈ (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0103 (f : Var) : (nb078_alpha_dummy_114 f) ∈ (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0104 : (nb078_alpha_dummy_110) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_110)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_111)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0105 (f : Var) : (nb078_alpha_dummy_113 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_113 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_114 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0106 : (nb078_alpha_dummy_110) ∈ (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_110))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0107 (f : Var) : (nb078_alpha_dummy_113 f) ∈ (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_113 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0108 : (nb078_alpha_dummy_111) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_110)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_111)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0109 (f : Var) : (nb078_alpha_dummy_114 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_113 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_114 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0110 : (nb078_alpha_dummy_111) ∈ (((Class.cv (nb078_alpha_dummy_111))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0111 (f : Var) : (nb078_alpha_dummy_114 f) ∈ (((Class.cv (nb078_alpha_dummy_114 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0112 : (nb078_alpha_dummy_090) ∈ (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0113 : (nb078_alpha_dummy_090) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0114 (f : Var) : (nb078_alpha_dummy_092 f) ∈ (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0115 (f : Var) : (nb078_alpha_dummy_092 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0116 : (nb078_alpha_dummy_090) ∈ (((Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0117 (f : Var) : (nb078_alpha_dummy_092 f) ∈ (((Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0118 : (nb078_alpha_dummy_096) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_096))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0119 (f : Var) : (nb078_alpha_dummy_098 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0120 : (nb078_alpha_dummy_096) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0121 (f : Var) : (nb078_alpha_dummy_098 f) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0122 : (nb078_alpha_dummy_090) ∈ (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0123 : (nb078_alpha_dummy_090) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0124 (f : Var) : (nb078_alpha_dummy_092 f) ∈ (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0125 (f : Var) : (nb078_alpha_dummy_092 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0126 : (nb078_alpha_dummy_090) ∈ (((Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0127 (f : Var) : (nb078_alpha_dummy_092 f) ∈ (((Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0128 : (nb078_alpha_dummy_132) ∈ (((Class.cv (nb078_alpha_dummy_132))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0129 (f : Var) : (nb078_alpha_dummy_134 f) ∈ (((Class.cv (nb078_alpha_dummy_134 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0130 : (nb078_alpha_dummy_139) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_139)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_139)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_139))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0131 (f : Var) : (nb078_alpha_dummy_141 f) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_141 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_141 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_141 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0132 : (nb078_alpha_dummy_139) ∈ (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0133 (f : Var) : (nb078_alpha_dummy_141 f) ∈ (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0134 : (nb078_alpha_dummy_146) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0135 (f : Var) : (nb078_alpha_dummy_149 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0136 : (nb078_alpha_dummy_146) ∈ (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0137 (f : Var) : (nb078_alpha_dummy_149 f) ∈ (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0138 : (nb078_alpha_dummy_147) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0139 (f : Var) : (nb078_alpha_dummy_150 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0140 : (nb078_alpha_dummy_147) ∈ (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0141 (f : Var) : (nb078_alpha_dummy_150 f) ∈ (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0142 : (nb078_alpha_dummy_146) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_146)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_147)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0143 (f : Var) : (nb078_alpha_dummy_149 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_149 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_150 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0144 : (nb078_alpha_dummy_146) ∈ (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_146))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0145 (f : Var) : (nb078_alpha_dummy_149 f) ∈ (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_149 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0146 : (nb078_alpha_dummy_147) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_146)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_147)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0147 (f : Var) : (nb078_alpha_dummy_150 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_149 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_150 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0148 : (nb078_alpha_dummy_147) ∈ (((Class.cv (nb078_alpha_dummy_147))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0149 (f : Var) : (nb078_alpha_dummy_150 f) ∈ (((Class.cv (nb078_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0150 : (nb078_alpha_dummy_089) ∈ (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0151 : (nb078_alpha_dummy_089) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0152 (f : Var) : (nb078_alpha_dummy_091 f) ∈ (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0153 (f : Var) : (nb078_alpha_dummy_091 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0154 : (nb078_alpha_dummy_089) ∈ (((Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0155 (f : Var) : (nb078_alpha_dummy_091 f) ∈ (((Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0156 : (nb078_alpha_dummy_132) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_132))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0157 (f : Var) : (nb078_alpha_dummy_134 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0158 : (nb078_alpha_dummy_132) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0159 (f : Var) : (nb078_alpha_dummy_134 f) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0160 : (nb078_alpha_dummy_000) ∈ (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0161 (f : Var) : f ∈ (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0162 : (nb078_alpha_dummy_000) ∈ (((syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0163 (f : Var) : f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0164 : (nb078_alpha_dummy_000) ∈ (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0165 : (nb078_alpha_dummy_000) ∈ (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000))) (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0164) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0166 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0167 (f : Var) : f ∈ (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb078_alpha_dummy_014 f))) (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_013 f)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0166 f) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0168 : (nb078_alpha_dummy_000) ∈ (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_089)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0169 (f : Var) : f ∈ (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_091 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0170 : (nb078_alpha_dummy_000) ∈ (((Class.cv (nb078_alpha_dummy_000))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
