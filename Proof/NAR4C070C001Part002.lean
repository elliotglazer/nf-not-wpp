import NAR4C070C001Part001

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

theorem nb070_support_mem_0011 (x : Var) : x ∈ (((syn_cpw (Class.cv x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0012 (A : Class) : (nb070_alpha_dummy_001 A) ∈ (((Class.cv (nb070_alpha_dummy_001 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0013 (x : Var) : x ∈ (((Class.cv x)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0014 (A : Class) : (nb070_alpha_dummy_001 A) ∈ (((syn_cnin (Class.cv (nb070_alpha_dummy_018 A)) (Class.cv (nb070_alpha_dummy_001 A)))).fv ∪ ((syn_cnin (Class.cv (nb070_alpha_dummy_018 A)) (Class.cv (nb070_alpha_dummy_001 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0015 (x : Var) : x ∈ (((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv ∪ ((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0016 (A : Class) : (nb070_alpha_dummy_001 A) ∈ (((Class.cv (nb070_alpha_dummy_018 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_001 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0017 (x : Var) : x ∈ (((Class.cv (nb070_alpha_dummy_019 x))).fv ∪ ((Class.cv x)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0018 (A : Class) : (nb070_alpha_dummy_009 A) ∈ (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_008 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0019 (A : Class) : (nb070_alpha_dummy_009 A) ∈ (((syn_ccompl (Class.cab (nb070_alpha_dummy_024 A) (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A)) (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A)) (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb070_alpha_dummy_024 A) (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A)) (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A)) (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0018 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0018 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0020 (x : Var) : (nb070_alpha_dummy_011 x) ∈ (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_010 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0021 (x : Var) : (nb070_alpha_dummy_011 x) ∈ (((syn_ccompl (Class.cab (nb070_alpha_dummy_026 x) (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x)) (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x)) (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb070_alpha_dummy_026 x) (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x)) (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x)) (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0020 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0020 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0022 (A : Class) : (nb070_alpha_dummy_009 A) ∈ (((Class.cab (nb070_alpha_dummy_024 A) (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A)) (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A)) (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_024 A) (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A)) (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A)) (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0018 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0018 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0023 (x : Var) : (nb070_alpha_dummy_011 x) ∈ (((Class.cab (nb070_alpha_dummy_026 x) (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x)) (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x)) (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_026 x) (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x)) (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x)) (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0020 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0020 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0024 (A : Class) : (nb070_alpha_dummy_025 A) ∈ (((Class.cv (nb070_alpha_dummy_025 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0025 (x : Var) : (nb070_alpha_dummy_027 x) ∈ (((Class.cv (nb070_alpha_dummy_027 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0026 (A : Class) : (nb070_alpha_dummy_032 A) ∈ (((Wff.classMem (Class.cv (nb070_alpha_dummy_032 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb070_alpha_dummy_032 A)) (syn_c1c))).fv ∪ ((Class.cv (nb070_alpha_dummy_032 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0027 (x : Var) : (nb070_alpha_dummy_034 x) ∈ (((Wff.classMem (Class.cv (nb070_alpha_dummy_034 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb070_alpha_dummy_034 x)) (syn_c1c))).fv ∪ ((Class.cv (nb070_alpha_dummy_034 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0028 (A : Class) : (nb070_alpha_dummy_032 A) ∈ (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0029 (x : Var) : (nb070_alpha_dummy_034 x) ∈ (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0030 (A : Class) : (nb070_alpha_dummy_039 A) ∈ (((syn_cnin (Class.cv (nb070_alpha_dummy_039 A)) (Class.cv (nb070_alpha_dummy_040 A)))).fv ∪ ((syn_cnin (Class.cv (nb070_alpha_dummy_039 A)) (Class.cv (nb070_alpha_dummy_040 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0031 (x : Var) : (nb070_alpha_dummy_042 x) ∈ (((syn_cnin (Class.cv (nb070_alpha_dummy_042 x)) (Class.cv (nb070_alpha_dummy_043 x)))).fv ∪ ((syn_cnin (Class.cv (nb070_alpha_dummy_042 x)) (Class.cv (nb070_alpha_dummy_043 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0032 (A : Class) : (nb070_alpha_dummy_039 A) ∈ (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_040 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0033 (x : Var) : (nb070_alpha_dummy_042 x) ∈ (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_043 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0034 (A : Class) : (nb070_alpha_dummy_040 A) ∈ (((syn_cnin (Class.cv (nb070_alpha_dummy_039 A)) (Class.cv (nb070_alpha_dummy_040 A)))).fv ∪ ((syn_cnin (Class.cv (nb070_alpha_dummy_039 A)) (Class.cv (nb070_alpha_dummy_040 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0035 (x : Var) : (nb070_alpha_dummy_043 x) ∈ (((syn_cnin (Class.cv (nb070_alpha_dummy_042 x)) (Class.cv (nb070_alpha_dummy_043 x)))).fv ∪ ((syn_cnin (Class.cv (nb070_alpha_dummy_042 x)) (Class.cv (nb070_alpha_dummy_043 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0036 (A : Class) : (nb070_alpha_dummy_040 A) ∈ (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_040 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0037 (x : Var) : (nb070_alpha_dummy_043 x) ∈ (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_043 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0038 (A : Class) : (nb070_alpha_dummy_039 A) ∈ (((syn_ccompl (Class.cv (nb070_alpha_dummy_039 A)))).fv ∪ ((syn_ccompl (Class.cv (nb070_alpha_dummy_040 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0039 (x : Var) : (nb070_alpha_dummy_042 x) ∈ (((syn_ccompl (Class.cv (nb070_alpha_dummy_042 x)))).fv ∪ ((syn_ccompl (Class.cv (nb070_alpha_dummy_043 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0040 (A : Class) : (nb070_alpha_dummy_039 A) ∈ (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_039 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0041 (x : Var) : (nb070_alpha_dummy_042 x) ∈ (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_042 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0042 (A : Class) : (nb070_alpha_dummy_040 A) ∈ (((syn_ccompl (Class.cv (nb070_alpha_dummy_039 A)))).fv ∪ ((syn_ccompl (Class.cv (nb070_alpha_dummy_040 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0043 (x : Var) : (nb070_alpha_dummy_043 x) ∈ (((syn_ccompl (Class.cv (nb070_alpha_dummy_042 x)))).fv ∪ ((syn_ccompl (Class.cv (nb070_alpha_dummy_043 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0044 (A : Class) : (nb070_alpha_dummy_040 A) ∈ (((Class.cv (nb070_alpha_dummy_040 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_040 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0045 (x : Var) : (nb070_alpha_dummy_043 x) ∈ (((Class.cv (nb070_alpha_dummy_043 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_043 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0046 (A : Class) : (nb070_alpha_dummy_008 A) ∈ (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_008 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0047 (A : Class) : (nb070_alpha_dummy_008 A) ∈ (((syn_ccompl (Class.cab (nb070_alpha_dummy_024 A) (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A)) (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A)) (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb070_alpha_dummy_024 A) (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A)) (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A)) (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0046 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0046 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0048 (x : Var) : (nb070_alpha_dummy_010 x) ∈ (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_010 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0049 (x : Var) : (nb070_alpha_dummy_010 x) ∈ (((syn_ccompl (Class.cab (nb070_alpha_dummy_026 x) (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x)) (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x)) (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb070_alpha_dummy_026 x) (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x)) (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x)) (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0048 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0048 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0050 (A : Class) : (nb070_alpha_dummy_008 A) ∈ (((Class.cab (nb070_alpha_dummy_024 A) (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A)) (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A)) (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_024 A) (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A)) (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A)) (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0046 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0046 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0051 (x : Var) : (nb070_alpha_dummy_010 x) ∈ (((Class.cab (nb070_alpha_dummy_026 x) (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x)) (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x)) (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_026 x) (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x)) (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x)) (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0048 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0048 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb070_support_mem_0052 (A : Class) : (nb070_alpha_dummy_025 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0053 (x : Var) : (nb070_alpha_dummy_027 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0054 (A : Class) : (nb070_alpha_dummy_025 A) ∈ (((syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))).fv ∪ ((syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0055 (x : Var) : (nb070_alpha_dummy_027 x) ∈ (((syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))).fv ∪ ((syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0056 (A : Class) : (nb070_alpha_dummy_002 A) ∈ (((Class.cv (nb070_alpha_dummy_002 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0057 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_003 x A b) ∈ (((Class.cv (nb070_alpha_dummy_003 x A b))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_compact_fv_empty_0000 (A : Class) : (nb070_alpha_dummy_000 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0000 (A : Class) : (nb070_alpha_dummy_000 A) ∉ ((syn_cncs)).fv := by
  simpa only [nb070_alpha_dummy_000, fv_syn_cncs] using (nb070_compact_fv_empty_0000 A)

theorem nb070_compact_fv_empty_0001 (b : Var) : b ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0001 (b : Var) : b ∉ ((syn_cncs)).fv := by
  simpa only [fv_syn_cncs] using (nb070_compact_fv_empty_0001 b)

theorem nb070_compact_fv_empty_0002 (A : Class) : (nb070_alpha_dummy_002 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0002 (A : Class) : (nb070_alpha_dummy_002 A) ∉ ((syn_cncs)).fv := by
  simpa only [nb070_alpha_dummy_002, fv_syn_cncs] using (nb070_compact_fv_empty_0002 A)

theorem nb070_compact_fv_empty_0003 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_003 x A b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0003 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_003 x A b) ∉ ((syn_cncs)).fv := by
  simpa only [nb070_alpha_dummy_003, fv_syn_cncs] using (nb070_compact_fv_empty_0003 x A b)

theorem nb070_compact_fv_empty_0004 (A : Class) : (nb070_alpha_dummy_005 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0004 (A : Class) : (nb070_alpha_dummy_005 A) ∉ ((syn_cncs)).fv := by
  simpa only [nb070_alpha_dummy_005, fv_syn_cncs] using (nb070_compact_fv_empty_0004 A)

theorem nb070_compact_fv_empty_0005 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_007 x A b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0005 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_007 x A b) ∉ ((syn_cncs)).fv := by
  simpa only [nb070_alpha_dummy_007, fv_syn_cncs] using (nb070_compact_fv_empty_0005 x A b)

theorem nb070_compact_fv_empty_0006 (A : Class) : (nb070_alpha_dummy_004 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0006 (A : Class) : (nb070_alpha_dummy_004 A) ∉ ((syn_cncs)).fv := by
  simpa only [nb070_alpha_dummy_004, fv_syn_cncs] using (nb070_compact_fv_empty_0006 A)

theorem nb070_compact_fv_empty_0007 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_006 x A b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0007 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_006 x A b) ∉ ((syn_cncs)).fv := by
  simpa only [nb070_alpha_dummy_006, fv_syn_cncs] using (nb070_compact_fv_empty_0007 x A b)

theorem nb070_compact_envfresh_0000 (x : Var) (A : Class) (b : Var) : TEnvFresh [((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_cncs)).fv := by
  exact (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0000 A) (nb070_wpp_notmem_0001 b) (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b) (nb070_wpp_notmem_0002 A) (nb070_wpp_notmem_0003 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b) (nb070_wpp_notmem_0004 A) (nb070_wpp_notmem_0005 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_006 x A b) (nb070_wpp_notmem_0006 A) (nb070_wpp_notmem_0007 x A b) (TEnvFresh.nil ((syn_cncs)).fv)))))

noncomputable def nb070_wpp_refl_0000 (x : Var) (A : Class) (b : Var) : TReflOn [((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_cncs)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0000 x A b)

theorem nb070_focused_notmem_0000 (A : Class) : (nb070_alpha_dummy_001 A) ∉ A.fv := by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => hu)

theorem nb070_wpp_notmem_0008 (A : Class) : (nb070_alpha_dummy_001 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0000 A)

theorem nb070_wpp_notmem_0009 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) : x ∉ (A).fv := by
  exact dv_A_x

theorem nb070_focused_notmem_0001 (A : Class) : (nb070_alpha_dummy_000 A) ∉ A.fv := by
  change freshVar ((A).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => hu)

theorem nb070_wpp_notmem_0010 (A : Class) : (nb070_alpha_dummy_000 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0001 A)

theorem nb070_wpp_notmem_0011 (A : Class) (b : Var) (dv_A_b : b ∉ A.fv) : b ∉ (A).fv := by
  exact dv_A_b

theorem nb070_focused_notmem_0002 (A : Class) : (nb070_alpha_dummy_002 A) ∉ A.fv := by
  change freshVar (({(nb070_alpha_dummy_000 A)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))).symm ▸ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb070_focused_notmem_0000 A)) (h_eq ▸ hu)), (hu)⟩))))))))

theorem nb070_wpp_notmem_0012 (A : Class) : (nb070_alpha_dummy_002 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0002 A)

theorem nb070_focused_notmem_0003 (x : Var) (A : Class) (b : Var) (dv_A_x : x ∉ A.fv) : (nb070_alpha_dummy_003 x A b) ∉ A.fv := by
  change freshVar (({b} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))).symm ▸ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)), (hu)⟩))))))))

theorem nb070_wpp_notmem_0013 (x : Var) (A : Class) (b : Var) (dv_A_x : x ∉ A.fv) : (nb070_alpha_dummy_003 x A b) ∉ (A).fv := by
  exact (nb070_focused_notmem_0003 x A b dv_A_x)

theorem nb070_focused_notmem_0004 (A : Class) : (nb070_alpha_dummy_005 A) ∉ A.fv := by
  change freshVar (((Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq (Class.cab (nb070_alpha_dummy_000 A) (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))) (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))))).fv) 1 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => ((fv_class_cab (nb070_alpha_dummy_002 A) (Wff.classEq (Class.cab (nb070_alpha_dummy_000 A) (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))) (syn_csn (Class.cv (nb070_alpha_dummy_002 A))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb070_focused_notmem_0002 A)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab (nb070_alpha_dummy_000 A) (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))) (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab (nb070_alpha_dummy_000 A) (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb070_focused_notmem_0001 A)) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))).symm ▸ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb070_focused_notmem_0000 A)) (h_eq ▸ hu)), (hu)⟩)))))))⟩))))))⟩)))

theorem nb070_wpp_notmem_0014 (A : Class) : (nb070_alpha_dummy_005 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0004 A)

theorem nb070_focused_notmem_0005 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) : (nb070_alpha_dummy_007 x A b) ∉ A.fv := by
  change freshVar (((Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))) (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))).fv) 1 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => ((fv_class_cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))) (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb070_focused_notmem_0003 x A b dv_A_x)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab b (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))) (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab b (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_A_b) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))).symm ▸ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)), (hu)⟩)))))))⟩))))))⟩)))

theorem nb070_wpp_notmem_0015 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) : (nb070_alpha_dummy_007 x A b) ∉ (A).fv := by
  exact (nb070_focused_notmem_0005 x A b dv_A_b dv_A_x)

theorem nb070_focused_notmem_0006 (A : Class) : (nb070_alpha_dummy_004 A) ∉ A.fv := by
  change freshVar (((Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq (Class.cab (nb070_alpha_dummy_000 A) (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))) (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => ((fv_class_cab (nb070_alpha_dummy_002 A) (Wff.classEq (Class.cab (nb070_alpha_dummy_000 A) (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))) (syn_csn (Class.cv (nb070_alpha_dummy_002 A))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb070_focused_notmem_0002 A)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab (nb070_alpha_dummy_000 A) (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))) (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab (nb070_alpha_dummy_000 A) (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb070_focused_notmem_0001 A)) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs)) (syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_wrex (nb070_alpha_dummy_001 A) A (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A)) (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))).symm ▸ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb070_focused_notmem_0000 A)) (h_eq ▸ hu)), (hu)⟩)))))))⟩))))))⟩)))

theorem nb070_wpp_notmem_0016 (A : Class) : (nb070_alpha_dummy_004 A) ∉ (A).fv := by
  exact (nb070_focused_notmem_0006 A)

theorem nb070_focused_notmem_0007 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) : (nb070_alpha_dummy_006 x A b) ∉ A.fv := by
  change freshVar (((Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))) (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))).fv) 0 ∉ A.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => ((fv_class_cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))) (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb070_focused_notmem_0003 x A b dv_A_x)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab b (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))) (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab b (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_A_b) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))).symm ▸ (Finset.mem_union_right _ (((fv_syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))).symm ▸ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_A_x) (h_eq ▸ hu)), (hu)⟩)))))))⟩))))))⟩)))

theorem nb070_wpp_notmem_0017 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) : (nb070_alpha_dummy_006 x A b) ∉ (A).fv := by
  exact (nb070_focused_notmem_0007 x A b dv_A_b dv_A_x)

theorem nb070_compact_envfresh_0001 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) : TEnvFresh [((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (A).fv := by
  exact (TEnvFresh.consFresh (nb070_alpha_dummy_001 A) x (nb070_wpp_notmem_0008 A) (nb070_wpp_notmem_0009 x A dv_A_x) (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0010 A) (nb070_wpp_notmem_0011 A b dv_A_b) (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b) (nb070_wpp_notmem_0012 A) (nb070_wpp_notmem_0013 x A b dv_A_x) (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b) (nb070_wpp_notmem_0014 A) (nb070_wpp_notmem_0015 x A b dv_A_b dv_A_x) (TEnvFresh.consFresh (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_006 x A b) (nb070_wpp_notmem_0016 A) (nb070_wpp_notmem_0017 x A b dv_A_b dv_A_x) (TEnvFresh.nil (A).fv))))))

noncomputable def nb070_wpp_refl_0001 (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) : TReflOn [((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (A).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0001 x A b dv_A_b dv_A_x)

theorem nb070_compact_fv_empty_0008 (A : Class) : (nb070_alpha_dummy_016 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0018 (A : Class) : (nb070_alpha_dummy_016 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_016, fv_syn_c1c] using (nb070_compact_fv_empty_0008 A)

theorem nb070_compact_fv_empty_0009 (x : Var) : (nb070_alpha_dummy_017 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0019 (x : Var) : (nb070_alpha_dummy_017 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_017, fv_syn_c1c] using (nb070_compact_fv_empty_0009 x)

theorem nb070_compact_fv_empty_0010 (A : Class) : (nb070_alpha_dummy_014 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0020 (A : Class) : (nb070_alpha_dummy_014 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_014, fv_syn_c1c] using (nb070_compact_fv_empty_0010 A)

theorem nb070_compact_fv_empty_0011 (x : Var) : (nb070_alpha_dummy_015 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0021 (x : Var) : (nb070_alpha_dummy_015 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_015, fv_syn_c1c] using (nb070_compact_fv_empty_0011 x)

theorem nb070_compact_fv_empty_0012 (A : Class) : (nb070_alpha_dummy_012 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0022 (A : Class) : (nb070_alpha_dummy_012 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_012, fv_syn_c1c] using (nb070_compact_fv_empty_0012 A)

theorem nb070_compact_fv_empty_0013 (x : Var) : (nb070_alpha_dummy_013 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0023 (x : Var) : (nb070_alpha_dummy_013 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_013, fv_syn_c1c] using (nb070_compact_fv_empty_0013 x)

theorem nb070_compact_fv_empty_0014 (A : Class) : (nb070_alpha_dummy_009 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0024 (A : Class) : (nb070_alpha_dummy_009 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_009, fv_syn_c1c] using (nb070_compact_fv_empty_0014 A)

theorem nb070_compact_fv_empty_0015 (x : Var) : (nb070_alpha_dummy_011 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0025 (x : Var) : (nb070_alpha_dummy_011 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_011, fv_syn_c1c] using (nb070_compact_fv_empty_0015 x)

theorem nb070_compact_fv_empty_0016 (A : Class) : (nb070_alpha_dummy_008 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0026 (A : Class) : (nb070_alpha_dummy_008 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_008, fv_syn_c1c] using (nb070_compact_fv_empty_0016 A)

theorem nb070_compact_fv_empty_0017 (x : Var) : (nb070_alpha_dummy_010 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0027 (x : Var) : (nb070_alpha_dummy_010 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_010, fv_syn_c1c] using (nb070_compact_fv_empty_0017 x)

theorem nb070_compact_fv_empty_0018 (A : Class) : (nb070_alpha_dummy_001 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0028 (A : Class) : (nb070_alpha_dummy_001 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_001, fv_syn_c1c] using (nb070_compact_fv_empty_0018 A)

theorem nb070_compact_fv_empty_0019 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0029 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb070_compact_fv_empty_0019 x)

theorem nb070_wpp_notmem_0030 (A : Class) : (nb070_alpha_dummy_000 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_000, fv_syn_c1c] using (nb070_compact_fv_empty_0000 A)

theorem nb070_wpp_notmem_0031 (b : Var) : b ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb070_compact_fv_empty_0001 b)

theorem nb070_wpp_notmem_0032 (A : Class) : (nb070_alpha_dummy_002 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_002, fv_syn_c1c] using (nb070_compact_fv_empty_0002 A)

theorem nb070_wpp_notmem_0033 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_003 x A b) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_003, fv_syn_c1c] using (nb070_compact_fv_empty_0003 x A b)

theorem nb070_wpp_notmem_0034 (A : Class) : (nb070_alpha_dummy_005 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_005, fv_syn_c1c] using (nb070_compact_fv_empty_0004 A)

theorem nb070_wpp_notmem_0035 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_007 x A b) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_007, fv_syn_c1c] using (nb070_compact_fv_empty_0005 x A b)

theorem nb070_wpp_notmem_0036 (A : Class) : (nb070_alpha_dummy_004 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_004, fv_syn_c1c] using (nb070_compact_fv_empty_0006 A)

theorem nb070_wpp_notmem_0037 (x : Var) (A : Class) (b : Var) : (nb070_alpha_dummy_006 x A b) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_006, fv_syn_c1c] using (nb070_compact_fv_empty_0007 x A b)

theorem nb070_compact_envfresh_0002 (x : Var) (A : Class) (b : Var) : TEnvFresh [((nb070_alpha_dummy_016 A), (nb070_alpha_dummy_017 x)), ((nb070_alpha_dummy_014 A), (nb070_alpha_dummy_015 x)), ((nb070_alpha_dummy_012 A), (nb070_alpha_dummy_013 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb070_alpha_dummy_016 A) (nb070_alpha_dummy_017 x) (nb070_wpp_notmem_0018 A) (nb070_wpp_notmem_0019 x) (TEnvFresh.consFresh (nb070_alpha_dummy_014 A) (nb070_alpha_dummy_015 x) (nb070_wpp_notmem_0020 A) (nb070_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb070_alpha_dummy_012 A) (nb070_alpha_dummy_013 x) (nb070_wpp_notmem_0022 A) (nb070_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb070_alpha_dummy_009 A) (nb070_alpha_dummy_011 x) (nb070_wpp_notmem_0024 A) (nb070_wpp_notmem_0025 x) (TEnvFresh.consFresh (nb070_alpha_dummy_008 A) (nb070_alpha_dummy_010 x) (nb070_wpp_notmem_0026 A) (nb070_wpp_notmem_0027 x) (TEnvFresh.consFresh (nb070_alpha_dummy_001 A) x (nb070_wpp_notmem_0028 A) (nb070_wpp_notmem_0029 x) (TEnvFresh.consFresh (nb070_alpha_dummy_000 A) b (nb070_wpp_notmem_0030 A) (nb070_wpp_notmem_0031 b) (TEnvFresh.consFresh (nb070_alpha_dummy_002 A) (nb070_alpha_dummy_003 x A b) (nb070_wpp_notmem_0032 A) (nb070_wpp_notmem_0033 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_005 A) (nb070_alpha_dummy_007 x A b) (nb070_wpp_notmem_0034 A) (nb070_wpp_notmem_0035 x A b) (TEnvFresh.consFresh (nb070_alpha_dummy_004 A) (nb070_alpha_dummy_006 x A b) (nb070_wpp_notmem_0036 A) (nb070_wpp_notmem_0037 x A b) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))

noncomputable def nb070_wpp_refl_0002 (x : Var) (A : Class) (b : Var) : TReflOn [((nb070_alpha_dummy_016 A), (nb070_alpha_dummy_017 x)), ((nb070_alpha_dummy_014 A), (nb070_alpha_dummy_015 x)), ((nb070_alpha_dummy_012 A), (nb070_alpha_dummy_013 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0002 x A b)

noncomputable def nb070_split_alpha_0000 (x : Var) (A : Class) (b : Var) : TAlphaWff [((nb070_alpha_dummy_014 A), (nb070_alpha_dummy_015 x)), ((nb070_alpha_dummy_012 A), (nb070_alpha_dummy_013 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (Wff.imp (Wff.classMem (Class.cv (nb070_alpha_dummy_014 A)) (syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))) (Wff.neg (Wff.classMem (Class.cv (nb070_alpha_dummy_014 A)) (syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))))) (Wff.imp (Wff.classMem (Class.cv (nb070_alpha_dummy_015 x)) (syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))) (Wff.neg (Wff.classMem (Class.cv (nb070_alpha_dummy_015 x)) (syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0002 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0003 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0014 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0015 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0013 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0010 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0011 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0008 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0009 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0006 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0007 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0002 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0003 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0014 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0015 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0013 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0010 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0011 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0008 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0009 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0006 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0007 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaClass.cv (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb070_alpha_dummy_016 A), (nb070_alpha_dummy_017 x)), ((nb070_alpha_dummy_014 A), (nb070_alpha_dummy_015 x)), ((nb070_alpha_dummy_012 A), (nb070_alpha_dummy_013 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (syn_c1c) (nb070_wpp_refl_0002 x A b))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0002 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0003 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0014 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0015 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0013 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0010 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0011 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0008 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0009 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0006 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0007 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0002 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0003 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0016 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0014 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0015 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0012 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0013 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0010 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0011 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0008 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0009 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0006 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0007 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaClass.cv (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb070_alpha_dummy_016 A), (nb070_alpha_dummy_017 x)), ((nb070_alpha_dummy_014 A), (nb070_alpha_dummy_015 x)), ((nb070_alpha_dummy_012 A), (nb070_alpha_dummy_013 x)), ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)), ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b), ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)), ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)), ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))] (syn_c1c) (nb070_wpp_refl_0002 x A b)))))))))))

theorem nb070_compact_fv_empty_0020 (A : Class) : (nb070_alpha_dummy_040 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0038 (A : Class) : (nb070_alpha_dummy_040 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_040, fv_syn_c1c] using (nb070_compact_fv_empty_0020 A)

theorem nb070_compact_fv_empty_0021 (x : Var) : (nb070_alpha_dummy_043 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0039 (x : Var) : (nb070_alpha_dummy_043 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_043, fv_syn_c1c] using (nb070_compact_fv_empty_0021 x)

theorem nb070_compact_fv_empty_0022 (A : Class) : (nb070_alpha_dummy_039 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0040 (A : Class) : (nb070_alpha_dummy_039 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_039, fv_syn_c1c] using (nb070_compact_fv_empty_0022 A)

theorem nb070_compact_fv_empty_0023 (x : Var) : (nb070_alpha_dummy_042 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0041 (x : Var) : (nb070_alpha_dummy_042 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_042, fv_syn_c1c] using (nb070_compact_fv_empty_0023 x)

theorem nb070_compact_fv_empty_0024 (A : Class) : (nb070_alpha_dummy_038 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0042 (A : Class) : (nb070_alpha_dummy_038 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_038, fv_syn_c1c] using (nb070_compact_fv_empty_0024 A)

theorem nb070_compact_fv_empty_0025 (x : Var) : (nb070_alpha_dummy_041 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0043 (x : Var) : (nb070_alpha_dummy_041 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_041, fv_syn_c1c] using (nb070_compact_fv_empty_0025 x)

theorem nb070_compact_fv_empty_0026 (A : Class) : (nb070_alpha_dummy_036 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0044 (A : Class) : (nb070_alpha_dummy_036 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_036, fv_syn_c1c] using (nb070_compact_fv_empty_0026 A)

theorem nb070_compact_fv_empty_0027 (x : Var) : (nb070_alpha_dummy_037 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0045 (x : Var) : (nb070_alpha_dummy_037 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_037, fv_syn_c1c] using (nb070_compact_fv_empty_0027 x)

theorem nb070_compact_fv_empty_0028 (A : Class) : (nb070_alpha_dummy_032 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0046 (A : Class) : (nb070_alpha_dummy_032 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_032, fv_syn_c1c] using (nb070_compact_fv_empty_0028 A)

theorem nb070_compact_fv_empty_0029 (x : Var) : (nb070_alpha_dummy_034 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0047 (x : Var) : (nb070_alpha_dummy_034 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_034, fv_syn_c1c] using (nb070_compact_fv_empty_0029 x)

theorem nb070_compact_fv_empty_0030 (A : Class) : (nb070_alpha_dummy_033 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0048 (A : Class) : (nb070_alpha_dummy_033 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_033, fv_syn_c1c] using (nb070_compact_fv_empty_0030 A)

theorem nb070_compact_fv_empty_0031 (x : Var) : (nb070_alpha_dummy_035 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0049 (x : Var) : (nb070_alpha_dummy_035 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_035, fv_syn_c1c] using (nb070_compact_fv_empty_0031 x)

theorem nb070_compact_fv_empty_0032 (A : Class) : (nb070_alpha_dummy_025 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0050 (A : Class) : (nb070_alpha_dummy_025 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_025, fv_syn_c1c] using (nb070_compact_fv_empty_0032 A)

theorem nb070_compact_fv_empty_0033 (x : Var) : (nb070_alpha_dummy_027 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0051 (x : Var) : (nb070_alpha_dummy_027 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_027, fv_syn_c1c] using (nb070_compact_fv_empty_0033 x)

theorem nb070_compact_fv_empty_0034 (A : Class) : (nb070_alpha_dummy_024 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb070_wpp_notmem_0052 (A : Class) : (nb070_alpha_dummy_024 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb070_alpha_dummy_024, fv_syn_c1c] using (nb070_compact_fv_empty_0034 A)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
