import NAR4C063C001Part002

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

theorem nb063_support_mem_0036 : (nb063_alpha_dummy_000) ∈ (((Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_000)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_000)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0037 (r : Var) (a : Var) : a ∈ (((Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0034 r a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0034 r a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0038 : (nb063_alpha_dummy_007) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0039 (r : Var) (a : Var) : (nb063_alpha_dummy_009 r a) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0040 : (nb063_alpha_dummy_007) ∈ (((syn_cphi (Class.cv (nb063_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_007)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0041 (r : Var) (a : Var) : (nb063_alpha_dummy_009 r a) ∈ (((syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0042 : (nb063_alpha_dummy_002) ∈ (((Class.cv (nb063_alpha_dummy_002))).fv ∪ ((Class.cv (nb063_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0043 : (nb063_alpha_dummy_002) ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cphi (Class.cv (nb063_alpha_dummy_043)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_043))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0042) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0042) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0044 (x : Var) (y : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0045 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0044 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0044 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0046 : (nb063_alpha_dummy_002) ∈ (((Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cphi (Class.cv (nb063_alpha_dummy_043))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cphi (Class.cv (nb063_alpha_dummy_043))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0042) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0042) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0047 (x : Var) (y : Var) : x ∈ (((Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0044 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0044 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0048 : (nb063_alpha_dummy_043) ∈ (((Class.cv (nb063_alpha_dummy_043))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0049 (x : Var) (y : Var) : (nb063_alpha_dummy_045 x y) ∈ (((Class.cv (nb063_alpha_dummy_045 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0050 : (nb063_alpha_dummy_050) ∈ (((Wff.classMem (Class.cv (nb063_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_050))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0051 (x : Var) (y : Var) : (nb063_alpha_dummy_052 x y) ∈ (((Wff.classMem (Class.cv (nb063_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_052 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0052 : (nb063_alpha_dummy_050) ∈ (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0053 (x : Var) (y : Var) : (nb063_alpha_dummy_052 x y) ∈ (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0054 : (nb063_alpha_dummy_057) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0055 (x : Var) (y : Var) : (nb063_alpha_dummy_060 x y) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_060 x y)) (Class.cv (nb063_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_060 x y)) (Class.cv (nb063_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0056 : (nb063_alpha_dummy_057) ∈ (((Class.cv (nb063_alpha_dummy_057))).fv ∪ ((Class.cv (nb063_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0057 (x : Var) (y : Var) : (nb063_alpha_dummy_060 x y) ∈ (((Class.cv (nb063_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0058 : (nb063_alpha_dummy_058) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0059 (x : Var) (y : Var) : (nb063_alpha_dummy_061 x y) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_060 x y)) (Class.cv (nb063_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_060 x y)) (Class.cv (nb063_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0060 : (nb063_alpha_dummy_058) ∈ (((Class.cv (nb063_alpha_dummy_057))).fv ∪ ((Class.cv (nb063_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0061 (x : Var) (y : Var) : (nb063_alpha_dummy_061 x y) ∈ (((Class.cv (nb063_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0062 : (nb063_alpha_dummy_057) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0063 (x : Var) (y : Var) : (nb063_alpha_dummy_060 x y) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0064 : (nb063_alpha_dummy_057) ∈ (((Class.cv (nb063_alpha_dummy_057))).fv ∪ ((Class.cv (nb063_alpha_dummy_057))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0065 (x : Var) (y : Var) : (nb063_alpha_dummy_060 x y) ∈ (((Class.cv (nb063_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_060 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0066 : (nb063_alpha_dummy_058) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0067 (x : Var) (y : Var) : (nb063_alpha_dummy_061 x y) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0068 : (nb063_alpha_dummy_058) ∈ (((Class.cv (nb063_alpha_dummy_058))).fv ∪ ((Class.cv (nb063_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0069 (x : Var) (y : Var) : (nb063_alpha_dummy_061 x y) ∈ (((Class.cv (nb063_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0070 : (nb063_alpha_dummy_003) ∈ (((Class.cv (nb063_alpha_dummy_002))).fv ∪ ((Class.cv (nb063_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0071 : (nb063_alpha_dummy_003) ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cphi (Class.cv (nb063_alpha_dummy_043)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_043))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0072 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0073 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0074 : (nb063_alpha_dummy_003) ∈ (((Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_043))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_043))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0075 (x : Var) (y : Var) : y ∈ (((Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0076 : (nb063_alpha_dummy_043) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_043))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0077 (x : Var) (y : Var) : (nb063_alpha_dummy_045 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0078 : (nb063_alpha_dummy_043) ∈ (((syn_cphi (Class.cv (nb063_alpha_dummy_043)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_043)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0079 (x : Var) (y : Var) : (nb063_alpha_dummy_045 x y) ∈ (((syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0080 : (nb063_alpha_dummy_003) ∈ (((Class.cv (nb063_alpha_dummy_003))).fv ∪ ((Class.cv (nb063_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0081 : (nb063_alpha_dummy_003) ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cphi (Class.cv (nb063_alpha_dummy_079)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_079))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0080) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0080) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0082 (x : Var) (y : Var) : y ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0083 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0082 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0082 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0084 : (nb063_alpha_dummy_003) ∈ (((Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cphi (Class.cv (nb063_alpha_dummy_079))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cphi (Class.cv (nb063_alpha_dummy_079))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0080) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0080) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0085 (x : Var) (y : Var) : y ∈ (((Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0082 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0082 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0086 : (nb063_alpha_dummy_079) ∈ (((Class.cv (nb063_alpha_dummy_079))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0087 (x : Var) (y : Var) : (nb063_alpha_dummy_081 x y) ∈ (((Class.cv (nb063_alpha_dummy_081 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0088 : (nb063_alpha_dummy_086) ∈ (((Wff.classMem (Class.cv (nb063_alpha_dummy_086)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_086)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_086))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0089 (x : Var) (y : Var) : (nb063_alpha_dummy_088 x y) ∈ (((Wff.classMem (Class.cv (nb063_alpha_dummy_088 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_088 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_088 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0090 : (nb063_alpha_dummy_086) ∈ (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0091 (x : Var) (y : Var) : (nb063_alpha_dummy_088 x y) ∈ (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0092 : (nb063_alpha_dummy_093) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0093 (x : Var) (y : Var) : (nb063_alpha_dummy_096 x y) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_096 x y)) (Class.cv (nb063_alpha_dummy_097 x y)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_096 x y)) (Class.cv (nb063_alpha_dummy_097 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0094 : (nb063_alpha_dummy_093) ∈ (((Class.cv (nb063_alpha_dummy_093))).fv ∪ ((Class.cv (nb063_alpha_dummy_094))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0095 (x : Var) (y : Var) : (nb063_alpha_dummy_096 x y) ∈ (((Class.cv (nb063_alpha_dummy_096 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_097 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0096 : (nb063_alpha_dummy_094) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0097 (x : Var) (y : Var) : (nb063_alpha_dummy_097 x y) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_096 x y)) (Class.cv (nb063_alpha_dummy_097 x y)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_096 x y)) (Class.cv (nb063_alpha_dummy_097 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0098 : (nb063_alpha_dummy_094) ∈ (((Class.cv (nb063_alpha_dummy_093))).fv ∪ ((Class.cv (nb063_alpha_dummy_094))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0099 (x : Var) (y : Var) : (nb063_alpha_dummy_097 x y) ∈ (((Class.cv (nb063_alpha_dummy_096 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_097 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0100 : (nb063_alpha_dummy_093) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_093)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_094)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0101 (x : Var) (y : Var) : (nb063_alpha_dummy_096 x y) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_096 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_097 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0102 : (nb063_alpha_dummy_093) ∈ (((Class.cv (nb063_alpha_dummy_093))).fv ∪ ((Class.cv (nb063_alpha_dummy_093))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0103 (x : Var) (y : Var) : (nb063_alpha_dummy_096 x y) ∈ (((Class.cv (nb063_alpha_dummy_096 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_096 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0104 : (nb063_alpha_dummy_094) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_093)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_094)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0105 (x : Var) (y : Var) : (nb063_alpha_dummy_097 x y) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_096 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_097 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0106 : (nb063_alpha_dummy_094) ∈ (((Class.cv (nb063_alpha_dummy_094))).fv ∪ ((Class.cv (nb063_alpha_dummy_094))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0107 (x : Var) (y : Var) : (nb063_alpha_dummy_097 x y) ∈ (((Class.cv (nb063_alpha_dummy_097 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_097 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0108 : (nb063_alpha_dummy_002) ∈ (((Class.cv (nb063_alpha_dummy_003))).fv ∪ ((Class.cv (nb063_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0109 : (nb063_alpha_dummy_002) ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cphi (Class.cv (nb063_alpha_dummy_079)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_079))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0110 (x : Var) (y : Var) : x ∈ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0111 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0112 : (nb063_alpha_dummy_002) ∈ (((Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_079))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_079))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0113 (x : Var) (y : Var) : x ∈ (((Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0114 : (nb063_alpha_dummy_079) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_079))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0115 (x : Var) (y : Var) : (nb063_alpha_dummy_081 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0116 : (nb063_alpha_dummy_079) ∈ (((syn_cphi (Class.cv (nb063_alpha_dummy_079)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_079)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0117 (x : Var) (y : Var) : (nb063_alpha_dummy_081 x y) ∈ (((syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_compact_fv_empty_0000 : (nb063_alpha_dummy_022) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0000 : (nb063_alpha_dummy_022) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_022, fv_syn_c1c] using (nb063_compact_fv_empty_0000)

theorem nb063_compact_fv_empty_0001 (r : Var) (a : Var) : (nb063_alpha_dummy_025 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0001 (r : Var) (a : Var) : (nb063_alpha_dummy_025 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_025, fv_syn_c1c] using (nb063_compact_fv_empty_0001 r a)

theorem nb063_compact_fv_empty_0002 : (nb063_alpha_dummy_021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0002 : (nb063_alpha_dummy_021) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_021, fv_syn_c1c] using (nb063_compact_fv_empty_0002)

theorem nb063_compact_fv_empty_0003 (r : Var) (a : Var) : (nb063_alpha_dummy_024 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0003 (r : Var) (a : Var) : (nb063_alpha_dummy_024 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_024, fv_syn_c1c] using (nb063_compact_fv_empty_0003 r a)

theorem nb063_compact_fv_empty_0004 : (nb063_alpha_dummy_020) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0004 : (nb063_alpha_dummy_020) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_020, fv_syn_c1c] using (nb063_compact_fv_empty_0004)

theorem nb063_compact_fv_empty_0005 (r : Var) (a : Var) : (nb063_alpha_dummy_023 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0005 (r : Var) (a : Var) : (nb063_alpha_dummy_023 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_023, fv_syn_c1c] using (nb063_compact_fv_empty_0005 r a)

theorem nb063_compact_fv_empty_0006 : (nb063_alpha_dummy_018) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0006 : (nb063_alpha_dummy_018) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_018, fv_syn_c1c] using (nb063_compact_fv_empty_0006)

theorem nb063_compact_fv_empty_0007 (r : Var) (a : Var) : (nb063_alpha_dummy_019 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0007 (r : Var) (a : Var) : (nb063_alpha_dummy_019 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_019, fv_syn_c1c] using (nb063_compact_fv_empty_0007 r a)

theorem nb063_compact_fv_empty_0008 : (nb063_alpha_dummy_014) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0008 : (nb063_alpha_dummy_014) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_014, fv_syn_c1c] using (nb063_compact_fv_empty_0008)

theorem nb063_compact_fv_empty_0009 (r : Var) (a : Var) : (nb063_alpha_dummy_016 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0009 (r : Var) (a : Var) : (nb063_alpha_dummy_016 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_016, fv_syn_c1c] using (nb063_compact_fv_empty_0009 r a)

theorem nb063_compact_fv_empty_0010 : (nb063_alpha_dummy_015) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0010 : (nb063_alpha_dummy_015) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_015, fv_syn_c1c] using (nb063_compact_fv_empty_0010)

theorem nb063_compact_fv_empty_0011 (r : Var) (a : Var) : (nb063_alpha_dummy_017 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0011 (r : Var) (a : Var) : (nb063_alpha_dummy_017 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_017, fv_syn_c1c] using (nb063_compact_fv_empty_0011 r a)

theorem nb063_compact_fv_empty_0012 : (nb063_alpha_dummy_007) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0012 : (nb063_alpha_dummy_007) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_007, fv_syn_c1c] using (nb063_compact_fv_empty_0012)

theorem nb063_compact_fv_empty_0013 (r : Var) (a : Var) : (nb063_alpha_dummy_009 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0013 (r : Var) (a : Var) : (nb063_alpha_dummy_009 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_009, fv_syn_c1c] using (nb063_compact_fv_empty_0013 r a)

theorem nb063_compact_fv_empty_0014 : (nb063_alpha_dummy_006) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0014 : (nb063_alpha_dummy_006) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_006, fv_syn_c1c] using (nb063_compact_fv_empty_0014)

theorem nb063_compact_fv_empty_0015 (r : Var) (a : Var) : (nb063_alpha_dummy_008 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0015 (r : Var) (a : Var) : (nb063_alpha_dummy_008 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_008, fv_syn_c1c] using (nb063_compact_fv_empty_0015 r a)

theorem nb063_compact_fv_empty_0016 : (nb063_alpha_dummy_012) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0016 : (nb063_alpha_dummy_012) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_012, fv_syn_c1c] using (nb063_compact_fv_empty_0016)

theorem nb063_compact_fv_empty_0017 (r : Var) (a : Var) : (nb063_alpha_dummy_013 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0017 (r : Var) (a : Var) : (nb063_alpha_dummy_013 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_013, fv_syn_c1c] using (nb063_compact_fv_empty_0017 r a)

theorem nb063_compact_fv_empty_0018 : (nb063_alpha_dummy_010) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0018 : (nb063_alpha_dummy_010) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_010, fv_syn_c1c] using (nb063_compact_fv_empty_0018)

theorem nb063_compact_fv_empty_0019 (r : Var) (a : Var) : (nb063_alpha_dummy_011 r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0019 (r : Var) (a : Var) : (nb063_alpha_dummy_011 r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_011, fv_syn_c1c] using (nb063_compact_fv_empty_0019 r a)

theorem nb063_compact_fv_empty_0020 : (nb063_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0020 : (nb063_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_000, fv_syn_c1c] using (nb063_compact_fv_empty_0020)

theorem nb063_compact_fv_empty_0021 (a : Var) : a ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0021 (a : Var) : a ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb063_compact_fv_empty_0021 a)

theorem nb063_compact_fv_empty_0022 : (nb063_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0022 : (nb063_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_001, fv_syn_c1c] using (nb063_compact_fv_empty_0022)

theorem nb063_compact_fv_empty_0023 (r : Var) : r ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0023 (r : Var) : r ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb063_compact_fv_empty_0023 r)

theorem nb063_compact_fv_empty_0024 : (nb063_alpha_dummy_004) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0024 : (nb063_alpha_dummy_004) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_004, fv_syn_c1c] using (nb063_compact_fv_empty_0024)

theorem nb063_compact_fv_empty_0025 (x : Var) (y : Var) (r : Var) (a : Var) : (nb063_alpha_dummy_005 x y r a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb063_wpp_notmem_0025 (x : Var) (y : Var) (r : Var) (a : Var) : (nb063_alpha_dummy_005 x y r a) ∉ ((syn_c1c)).fv := by
  simpa only [nb063_alpha_dummy_005, fv_syn_c1c] using (nb063_compact_fv_empty_0025 x y r a)

theorem nb063_compact_envfresh_0000 (x : Var) (y : Var) (r : Var) (a : Var) : TEnvFresh [((nb063_alpha_dummy_022), (nb063_alpha_dummy_025 r a)), ((nb063_alpha_dummy_021), (nb063_alpha_dummy_024 r a)), ((nb063_alpha_dummy_020), (nb063_alpha_dummy_023 r a)), ((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)), ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)), ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)), ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)), ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)), ((nb063_alpha_dummy_012), (nb063_alpha_dummy_013 r a)), ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)), ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r), ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb063_alpha_dummy_022) (nb063_alpha_dummy_025 r a) (nb063_wpp_notmem_0000) (nb063_wpp_notmem_0001 r a) (TEnvFresh.consFresh (nb063_alpha_dummy_021) (nb063_alpha_dummy_024 r a) (nb063_wpp_notmem_0002) (nb063_wpp_notmem_0003 r a) (TEnvFresh.consFresh (nb063_alpha_dummy_020) (nb063_alpha_dummy_023 r a) (nb063_wpp_notmem_0004) (nb063_wpp_notmem_0005 r a) (TEnvFresh.consFresh (nb063_alpha_dummy_018) (nb063_alpha_dummy_019 r a) (nb063_wpp_notmem_0006) (nb063_wpp_notmem_0007 r a) (TEnvFresh.consFresh (nb063_alpha_dummy_014) (nb063_alpha_dummy_016 r a) (nb063_wpp_notmem_0008) (nb063_wpp_notmem_0009 r a) (TEnvFresh.consFresh (nb063_alpha_dummy_015) (nb063_alpha_dummy_017 r a) (nb063_wpp_notmem_0010) (nb063_wpp_notmem_0011 r a) (TEnvFresh.consFresh (nb063_alpha_dummy_007) (nb063_alpha_dummy_009 r a) (nb063_wpp_notmem_0012) (nb063_wpp_notmem_0013 r a) (TEnvFresh.consFresh (nb063_alpha_dummy_006) (nb063_alpha_dummy_008 r a) (nb063_wpp_notmem_0014) (nb063_wpp_notmem_0015 r a) (TEnvFresh.consFresh (nb063_alpha_dummy_012) (nb063_alpha_dummy_013 r a) (nb063_wpp_notmem_0016) (nb063_wpp_notmem_0017 r a) (TEnvFresh.consFresh (nb063_alpha_dummy_010) (nb063_alpha_dummy_011 r a) (nb063_wpp_notmem_0018) (nb063_wpp_notmem_0019 r a) (TEnvFresh.consFresh (nb063_alpha_dummy_000) a (nb063_wpp_notmem_0020) (nb063_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb063_alpha_dummy_001) r (nb063_wpp_notmem_0022) (nb063_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb063_alpha_dummy_004) (nb063_alpha_dummy_005 x y r a) (nb063_wpp_notmem_0024) (nb063_wpp_notmem_0025 x y r a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb063_wpp_refl_0000 (x : Var) (y : Var) (r : Var) (a : Var) : TReflOn [((nb063_alpha_dummy_022), (nb063_alpha_dummy_025 r a)), ((nb063_alpha_dummy_021), (nb063_alpha_dummy_024 r a)), ((nb063_alpha_dummy_020), (nb063_alpha_dummy_023 r a)), ((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)), ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)), ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)), ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)), ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)), ((nb063_alpha_dummy_012), (nb063_alpha_dummy_013 r a)), ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)), ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r), ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb063_compact_envfresh_0000 x y r a)

theorem nb063_wpp_notmem_0026 : (nb063_alpha_dummy_022) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_022, fv_syn_c0] using (nb063_compact_fv_empty_0000)

theorem nb063_wpp_notmem_0027 (r : Var) (a : Var) : (nb063_alpha_dummy_025 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_025, fv_syn_c0] using (nb063_compact_fv_empty_0001 r a)

theorem nb063_wpp_notmem_0028 : (nb063_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_021, fv_syn_c0] using (nb063_compact_fv_empty_0002)

theorem nb063_wpp_notmem_0029 (r : Var) (a : Var) : (nb063_alpha_dummy_024 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_024, fv_syn_c0] using (nb063_compact_fv_empty_0003 r a)

theorem nb063_wpp_notmem_0030 : (nb063_alpha_dummy_020) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_020, fv_syn_c0] using (nb063_compact_fv_empty_0004)

theorem nb063_wpp_notmem_0031 (r : Var) (a : Var) : (nb063_alpha_dummy_023 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_023, fv_syn_c0] using (nb063_compact_fv_empty_0005 r a)

theorem nb063_wpp_notmem_0032 : (nb063_alpha_dummy_018) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_018, fv_syn_c0] using (nb063_compact_fv_empty_0006)

theorem nb063_wpp_notmem_0033 (r : Var) (a : Var) : (nb063_alpha_dummy_019 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_019, fv_syn_c0] using (nb063_compact_fv_empty_0007 r a)

theorem nb063_wpp_notmem_0034 : (nb063_alpha_dummy_014) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_014, fv_syn_c0] using (nb063_compact_fv_empty_0008)

theorem nb063_wpp_notmem_0035 (r : Var) (a : Var) : (nb063_alpha_dummy_016 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_016, fv_syn_c0] using (nb063_compact_fv_empty_0009 r a)

theorem nb063_wpp_notmem_0036 : (nb063_alpha_dummy_015) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_015, fv_syn_c0] using (nb063_compact_fv_empty_0010)

theorem nb063_wpp_notmem_0037 (r : Var) (a : Var) : (nb063_alpha_dummy_017 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_017, fv_syn_c0] using (nb063_compact_fv_empty_0011 r a)

theorem nb063_wpp_notmem_0038 : (nb063_alpha_dummy_007) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_007, fv_syn_c0] using (nb063_compact_fv_empty_0012)

theorem nb063_wpp_notmem_0039 (r : Var) (a : Var) : (nb063_alpha_dummy_009 r a) ∉ ((syn_c0)).fv := by
  simpa only [nb063_alpha_dummy_009, fv_syn_c0] using (nb063_compact_fv_empty_0013 r a)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
