import NAR4C076C001Part003

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

theorem nb076_support_mem_0048 : (nb076_alpha_dummy_004) ∈ (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0049 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : n ∈ (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0050 : (nb076_alpha_dummy_004) ∈ (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0051 : (nb076_alpha_dummy_004) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0052 (m : Var) (n : Var) : n ∈ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0053 (m : Var) (n : Var) : n ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0054 : (nb076_alpha_dummy_004) ∈ (((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017) (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004)) (Wff.classEq (Class.cv (nb076_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0055 (m : Var) (n : Var) : n ∈ (((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n) (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0056 : (nb076_alpha_dummy_018) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_018))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0057 (m : Var) (n : Var) : (nb076_alpha_dummy_020 m n) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0058 : (nb076_alpha_dummy_018) ∈ (((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0059 (m : Var) (n : Var) : (nb076_alpha_dummy_020 m n) ∈ (((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0060 : (nb076_alpha_dummy_010) ∈ (((Class.cv (nb076_alpha_dummy_010))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0061 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_012 g m n a b) ∈ (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0062 : (nb076_alpha_dummy_053) ∈ (((Wff.classMem (Class.cv (nb076_alpha_dummy_053)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_053)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_053))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0063 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_055 g m n a b) ∈ (((Wff.classMem (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0064 : (nb076_alpha_dummy_053) ∈ (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0065 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_055 g m n a b) ∈ (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0066 : (nb076_alpha_dummy_060) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0067 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_063 g m n a b) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b)) (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b)) (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0068 : (nb076_alpha_dummy_060) ∈ (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0069 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_063 g m n a b) ∈ (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0070 : (nb076_alpha_dummy_061) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0071 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_064 g m n a b) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b)) (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b)) (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0072 : (nb076_alpha_dummy_061) ∈ (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0073 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_064 g m n a b) ∈ (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0074 : (nb076_alpha_dummy_060) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_061)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0075 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_063 g m n a b) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_063 g m n a b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0076 : (nb076_alpha_dummy_060) ∈ (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_060))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0077 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_063 g m n a b) ∈ (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0078 : (nb076_alpha_dummy_061) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_060)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_061)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0079 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_064 g m n a b) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_063 g m n a b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0080 : (nb076_alpha_dummy_061) ∈ (((Class.cv (nb076_alpha_dummy_061))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0081 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_064 g m n a b) ∈ (((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0082 : (nb076_alpha_dummy_005) ∈ (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0083 : (nb076_alpha_dummy_005) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004))) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0084 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_006 g m n a b) ∈ (((syn_cop (Class.cv m) (Class.cv n))).fv ∪ ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0085 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_006 g m n a b) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0086 : (nb076_alpha_dummy_005) ∈ (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005)) (Wff.classEq (Class.cv (nb076_alpha_dummy_009)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0087 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_006 g m n a b) ∈ (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b) (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0088 : (nb076_alpha_dummy_010) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_010))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0089 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_012 g m n a b) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0090 : (nb076_alpha_dummy_010) ∈ (((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0091 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_012 g m n a b) ∈ (((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0092 : (nb076_alpha_dummy_000) ∈ (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0093 : (nb076_alpha_dummy_000) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0094 (g : Var) (a : Var) (b : Var) : a ∈ (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0095 (g : Var) (a : Var) (b : Var) : a ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0096 : (nb076_alpha_dummy_000) ∈ (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0097 (g : Var) (a : Var) (b : Var) : a ∈ (((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0098 : (nb076_alpha_dummy_082) ∈ (((Class.cv (nb076_alpha_dummy_082))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0099 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_084 g a b) ∈ (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0100 : (nb076_alpha_dummy_089) ∈ (((Wff.classMem (Class.cv (nb076_alpha_dummy_089)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_089)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_089))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0101 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_091 g a b) ∈ (((Wff.classMem (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_091 g a b))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0102 : (nb076_alpha_dummy_089) ∈ (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0103 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_091 g a b) ∈ (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0104 : (nb076_alpha_dummy_096) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0105 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_099 g a b) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b)) (Class.cv (nb076_alpha_dummy_100 g a b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b)) (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0106 : (nb076_alpha_dummy_096) ∈ (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0107 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_099 g a b) ∈ (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0108 : (nb076_alpha_dummy_097) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0109 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_100 g a b) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b)) (Class.cv (nb076_alpha_dummy_100 g a b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b)) (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0110 : (nb076_alpha_dummy_097) ∈ (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0111 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_100 g a b) ∈ (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0112 : (nb076_alpha_dummy_096) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_096)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_097)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0113 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_099 g a b) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_099 g a b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0114 : (nb076_alpha_dummy_096) ∈ (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_096))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0115 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_099 g a b) ∈ (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_099 g a b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0116 : (nb076_alpha_dummy_097) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_096)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_097)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0117 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_100 g a b) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_099 g a b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0118 : (nb076_alpha_dummy_097) ∈ (((Class.cv (nb076_alpha_dummy_097))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0119 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_100 g a b) ∈ (((Class.cv (nb076_alpha_dummy_100 g a b))).fv ∪ ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0120 : (nb076_alpha_dummy_113) ∈ (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113)) (Class.cv (nb076_alpha_dummy_001))) (Wff.classMem (Class.cv (nb076_alpha_dummy_114)) (Class.cv (nb076_alpha_dummy_002))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0121 (g : Var) (b : Var) : (nb076_alpha_dummy_115 g b) ∈ (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪ ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b)) (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0122 : (nb076_alpha_dummy_114) ∈ (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113)) (Class.cv (nb076_alpha_dummy_001))) (Wff.classMem (Class.cv (nb076_alpha_dummy_114)) (Class.cv (nb076_alpha_dummy_002))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0123 (g : Var) (b : Var) : (nb076_alpha_dummy_116 g b) ∈ (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪ ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b)) (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0124 : (nb076_alpha_dummy_113) ∈ (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0125 : (nb076_alpha_dummy_113) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0126 (g : Var) (b : Var) : (nb076_alpha_dummy_115 g b) ∈ (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_116 g b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0127 (g : Var) (b : Var) : (nb076_alpha_dummy_115 g b) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0128 : (nb076_alpha_dummy_113) ∈ (((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0129 (g : Var) (b : Var) : (nb076_alpha_dummy_115 g b) ∈ (((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0130 : (nb076_alpha_dummy_120) ∈ (((Class.cv (nb076_alpha_dummy_120))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0131 (g : Var) (b : Var) : (nb076_alpha_dummy_122 g b) ∈ (((Class.cv (nb076_alpha_dummy_122 g b))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0132 : (nb076_alpha_dummy_127) ∈ (((Wff.classMem (Class.cv (nb076_alpha_dummy_127)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_127)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_127))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0133 (g : Var) (b : Var) : (nb076_alpha_dummy_129 g b) ∈ (((Wff.classMem (Class.cv (nb076_alpha_dummy_129 g b)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb076_alpha_dummy_129 g b)) (syn_c1c))).fv ∪ ((Class.cv (nb076_alpha_dummy_129 g b))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0134 : (nb076_alpha_dummy_127) ∈ (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0135 (g : Var) (b : Var) : (nb076_alpha_dummy_129 g b) ∈ (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0136 : (nb076_alpha_dummy_134) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0137 (g : Var) (b : Var) : (nb076_alpha_dummy_137 g b) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b)) (Class.cv (nb076_alpha_dummy_138 g b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b)) (Class.cv (nb076_alpha_dummy_138 g b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0138 : (nb076_alpha_dummy_134) ∈ (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0139 (g : Var) (b : Var) : (nb076_alpha_dummy_137 g b) ∈ (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_138 g b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0140 : (nb076_alpha_dummy_135) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0141 (g : Var) (b : Var) : (nb076_alpha_dummy_138 g b) ∈ (((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b)) (Class.cv (nb076_alpha_dummy_138 g b)))).fv ∪ ((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b)) (Class.cv (nb076_alpha_dummy_138 g b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0142 : (nb076_alpha_dummy_135) ∈ (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0143 (g : Var) (b : Var) : (nb076_alpha_dummy_138 g b) ∈ (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_138 g b))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0144 : (nb076_alpha_dummy_134) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_134)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_135)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0145 (g : Var) (b : Var) : (nb076_alpha_dummy_137 g b) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_137 g b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_138 g b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0146 : (nb076_alpha_dummy_134) ∈ (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_134))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0147 (g : Var) (b : Var) : (nb076_alpha_dummy_137 g b) ∈ (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_137 g b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0148 : (nb076_alpha_dummy_135) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_134)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_135)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0149 (g : Var) (b : Var) : (nb076_alpha_dummy_138 g b) ∈ (((syn_ccompl (Class.cv (nb076_alpha_dummy_137 g b)))).fv ∪ ((syn_ccompl (Class.cv (nb076_alpha_dummy_138 g b)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0150 : (nb076_alpha_dummy_135) ∈ (((Class.cv (nb076_alpha_dummy_135))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0151 (g : Var) (b : Var) : (nb076_alpha_dummy_138 g b) ∈ (((Class.cv (nb076_alpha_dummy_138 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_138 g b))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0152 : (nb076_alpha_dummy_114) ∈ (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0153 : (nb076_alpha_dummy_114) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0154 (g : Var) (b : Var) : (nb076_alpha_dummy_116 g b) ∈ (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪ ((Class.cv (nb076_alpha_dummy_116 g b))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0155 (g : Var) (b : Var) : (nb076_alpha_dummy_116 g b) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0156 : (nb076_alpha_dummy_114) ∈ (((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119) (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114)) (Wff.classEq (Class.cv (nb076_alpha_dummy_119)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0157 (g : Var) (b : Var) : (nb076_alpha_dummy_116 g b) ∈ (((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b) (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b)) (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0158 : (nb076_alpha_dummy_120) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_120))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0159 (g : Var) (b : Var) : (nb076_alpha_dummy_122 g b) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0160 : (nb076_alpha_dummy_120) ∈ (((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0161 (g : Var) (b : Var) : (nb076_alpha_dummy_122 g b) ∈ (((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv ∪ ((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0162 : (nb076_alpha_dummy_001) ∈ (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_cxp]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0163 : (nb076_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 1))
    ·
      rw [fv_syn_cxp]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0164 (g : Var) (a : Var) (b : Var) : b ∈ (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_cxp]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0165 (g : Var) (a : Var) (b : Var) : b ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 1))
    ·
      rw [fv_syn_cxp]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0166 : (nb076_alpha_dummy_001) ∈ (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 1))
    ·
      rw [fv_syn_cxp]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0167 (g : Var) (a : Var) (b : Var) : b ∈ (((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 1))
    ·
      rw [fv_syn_cxp]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0168 : (nb076_alpha_dummy_001) ∈ (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113)) (Class.cv (nb076_alpha_dummy_001))) (Wff.classMem (Class.cv (nb076_alpha_dummy_114)) (Class.cv (nb076_alpha_dummy_002))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wa]
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0169 (g : Var) (b : Var) : b ∈ (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪ ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b)) (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wa]
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0170 : (nb076_alpha_dummy_001) ∈ (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0171 (g : Var) (b : Var) : b ∈ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0172 : (nb076_alpha_dummy_002) ∈ (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_cxp]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0173 : (nb076_alpha_dummy_002) ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002))) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 1))
    ·
      rw [fv_syn_cxp]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0174 (g : Var) (a : Var) (b : Var) : g ∈ (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_cxp]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0175 (g : Var) (a : Var) (b : Var) : g ∈ (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g)) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 1))
    ·
      rw [fv_syn_cxp]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
