import NAR4C073C001Part002

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

theorem nb073_support_mem_0033 (x : Var) (y : Var) : (nb073_alpha_dummy_033 x y) ∈ (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_033 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0034 : (nb073_alpha_dummy_029) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_030)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0035 (x : Var) (y : Var) : (nb073_alpha_dummy_032 x y) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_033 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0036 : (nb073_alpha_dummy_029) ∈ (((Class.cv (nb073_alpha_dummy_029))).fv ∪ ((Class.cv (nb073_alpha_dummy_029))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0037 (x : Var) (y : Var) : (nb073_alpha_dummy_032 x y) ∈ (((Class.cv (nb073_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_032 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0038 : (nb073_alpha_dummy_030) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_030)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0039 (x : Var) (y : Var) : (nb073_alpha_dummy_033 x y) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_033 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0040 : (nb073_alpha_dummy_030) ∈ (((Class.cv (nb073_alpha_dummy_030))).fv ∪ ((Class.cv (nb073_alpha_dummy_030))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0041 (x : Var) (y : Var) : (nb073_alpha_dummy_033 x y) ∈ (((Class.cv (nb073_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_033 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0042 : (nb073_alpha_dummy_001) ∈ (({(nb073_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb073_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cxp (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0043 (x : Var) (y : Var) : y ∈ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cxp (Class.cv x) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0044 : (nb073_alpha_dummy_001) ∈ (((syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv ∪ ((Class.cv (nb073_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0045 : (nb073_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007) (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001))) (Wff.classEq (Class.cv (nb073_alpha_dummy_006)) (syn_cphi (Class.cv (nb073_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002)) (Wff.classEq (Class.cv (nb073_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0046 (x : Var) (y : Var) : y ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb073_alpha_dummy_003 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0047 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb073_alpha_dummy_008 x y) (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb073_alpha_dummy_008 x y) (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0048 : (nb073_alpha_dummy_001) ∈ (((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007) (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001))) (Wff.classEq (Class.cv (nb073_alpha_dummy_006)) (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007) (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001))) (Wff.classEq (Class.cv (nb073_alpha_dummy_006)) (syn_cphi (Class.cv (nb073_alpha_dummy_007))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0044) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0049 (x : Var) (y : Var) : y ∈ (((Class.cab (nb073_alpha_dummy_008 x y) (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_008 x y) (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0046 x y) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0050 : (nb073_alpha_dummy_001) ∈ (((Class.cv (nb073_alpha_dummy_000))).fv ∪ ((Class.cv (nb073_alpha_dummy_001))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0051 : (nb073_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb073_alpha_dummy_014) (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000)) (Wff.classEq (Class.cv (nb073_alpha_dummy_014)) (syn_cphi (Class.cv (nb073_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb073_alpha_dummy_014) (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001)) (Wff.classEq (Class.cv (nb073_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0052 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0053 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb073_alpha_dummy_016 x y) (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb073_alpha_dummy_016 x y) (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0054 : (nb073_alpha_dummy_001) ∈ (((Class.cab (nb073_alpha_dummy_014) (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001)) (Wff.classEq (Class.cv (nb073_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_014) (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_001)) (Wff.classEq (Class.cv (nb073_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0050) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0055 (x : Var) (y : Var) : y ∈ (((Class.cab (nb073_alpha_dummy_016 x y) (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_016 x y) (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0052 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0056 : (nb073_alpha_dummy_015) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_015))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0057 (x : Var) (y : Var) : (nb073_alpha_dummy_017 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0058 : (nb073_alpha_dummy_015) ∈ (((syn_cphi (Class.cv (nb073_alpha_dummy_015)))).fv ∪ ((syn_cphi (Class.cv (nb073_alpha_dummy_015)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0059 (x : Var) (y : Var) : (nb073_alpha_dummy_017 x y) ∈ (((syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))).fv ∪ ((syn_cphi (Class.cv (nb073_alpha_dummy_017 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0060 : (nb073_alpha_dummy_007) ∈ (((Class.cv (nb073_alpha_dummy_007))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0061 (x : Var) (y : Var) : (nb073_alpha_dummy_009 x y) ∈ (((Class.cv (nb073_alpha_dummy_009 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0062 : (nb073_alpha_dummy_050) ∈ (((Wff.classMem (Class.cv (nb073_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb073_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb073_alpha_dummy_050))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0063 (x : Var) (y : Var) : (nb073_alpha_dummy_052 x y) ∈ (((Wff.classMem (Class.cv (nb073_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb073_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb073_alpha_dummy_052 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0064 : (nb073_alpha_dummy_050) ∈ (((Class.cv (nb073_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0065 (x : Var) (y : Var) : (nb073_alpha_dummy_052 x y) ∈ (((Class.cv (nb073_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0066 : (nb073_alpha_dummy_057) ∈ (((syn_cnin (Class.cv (nb073_alpha_dummy_057)) (Class.cv (nb073_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb073_alpha_dummy_057)) (Class.cv (nb073_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0067 (x : Var) (y : Var) : (nb073_alpha_dummy_060 x y) ∈ (((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y)) (Class.cv (nb073_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y)) (Class.cv (nb073_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0068 : (nb073_alpha_dummy_057) ∈ (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0069 (x : Var) (y : Var) : (nb073_alpha_dummy_060 x y) ∈ (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0070 : (nb073_alpha_dummy_058) ∈ (((syn_cnin (Class.cv (nb073_alpha_dummy_057)) (Class.cv (nb073_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb073_alpha_dummy_057)) (Class.cv (nb073_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0071 (x : Var) (y : Var) : (nb073_alpha_dummy_061 x y) ∈ (((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y)) (Class.cv (nb073_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb073_alpha_dummy_060 x y)) (Class.cv (nb073_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0072 : (nb073_alpha_dummy_058) ∈ (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0073 (x : Var) (y : Var) : (nb073_alpha_dummy_061 x y) ∈ (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0074 : (nb073_alpha_dummy_057) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0075 (x : Var) (y : Var) : (nb073_alpha_dummy_060 x y) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0076 : (nb073_alpha_dummy_057) ∈ (((Class.cv (nb073_alpha_dummy_057))).fv ∪ ((Class.cv (nb073_alpha_dummy_057))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0077 (x : Var) (y : Var) : (nb073_alpha_dummy_060 x y) ∈ (((Class.cv (nb073_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_060 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0078 : (nb073_alpha_dummy_058) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0079 (x : Var) (y : Var) : (nb073_alpha_dummy_061 x y) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0080 : (nb073_alpha_dummy_058) ∈ (((Class.cv (nb073_alpha_dummy_058))).fv ∪ ((Class.cv (nb073_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0081 (x : Var) (y : Var) : (nb073_alpha_dummy_061 x y) ∈ (((Class.cv (nb073_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0082 : (nb073_alpha_dummy_002) ∈ (((syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001)))).fv ∪ ((Class.cv (nb073_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0083 : (nb073_alpha_dummy_002) ∈ (((syn_ccompl (Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007) (syn_cop (Class.cv (nb073_alpha_dummy_000)) (Class.cv (nb073_alpha_dummy_001))) (Wff.classEq (Class.cv (nb073_alpha_dummy_006)) (syn_cphi (Class.cv (nb073_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002)) (Wff.classEq (Class.cv (nb073_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0084 (x : Var) (y : Var) : (nb073_alpha_dummy_003 x y) ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb073_alpha_dummy_003 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0085 (x : Var) (y : Var) : (nb073_alpha_dummy_003 x y) ∈ (((syn_ccompl (Class.cab (nb073_alpha_dummy_008 x y) (syn_wrex (nb073_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb073_alpha_dummy_008 x y) (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0086 : (nb073_alpha_dummy_002) ∈ (((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002)) (Wff.classEq (Class.cv (nb073_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_006) (syn_wrex (nb073_alpha_dummy_007) (Class.cv (nb073_alpha_dummy_002)) (Wff.classEq (Class.cv (nb073_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_007))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0082) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0087 (x : Var) (y : Var) : (nb073_alpha_dummy_003 x y) ∈ (((Class.cab (nb073_alpha_dummy_008 x y) (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_008 x y) (syn_wrex (nb073_alpha_dummy_009 x y) (Class.cv (nb073_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0084 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0088 : (nb073_alpha_dummy_007) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0089 (x : Var) (y : Var) : (nb073_alpha_dummy_009 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_009 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0090 : (nb073_alpha_dummy_007) ∈ (((syn_cphi (Class.cv (nb073_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb073_alpha_dummy_007)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0091 (x : Var) (y : Var) : (nb073_alpha_dummy_009 x y) ∈ (((syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))).fv ∪ ((syn_cphi (Class.cv (nb073_alpha_dummy_009 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0092 : (nb073_alpha_dummy_014) ∈ (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014)) (Class.cv (nb073_alpha_dummy_000))) (Wff.classMem (Class.cv (nb073_alpha_dummy_015)) (Class.cv (nb073_alpha_dummy_001))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0093 (x : Var) (y : Var) : (nb073_alpha_dummy_016 x y) ∈ (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x)) (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0094 : (nb073_alpha_dummy_015) ∈ (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014)) (Class.cv (nb073_alpha_dummy_000))) (Wff.classMem (Class.cv (nb073_alpha_dummy_015)) (Class.cv (nb073_alpha_dummy_001))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0095 (x : Var) (y : Var) : (nb073_alpha_dummy_017 x y) ∈ (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x)) (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0096 : (nb073_alpha_dummy_014) ∈ (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0097 : (nb073_alpha_dummy_014) ∈ (((syn_ccompl (Class.cab (nb073_alpha_dummy_080) (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014)) (Wff.classEq (Class.cv (nb073_alpha_dummy_080)) (syn_cphi (Class.cv (nb073_alpha_dummy_081)))))))).fv ∪ ((syn_ccompl (Class.cab (nb073_alpha_dummy_080) (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015)) (Wff.classEq (Class.cv (nb073_alpha_dummy_080)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0098 (x : Var) (y : Var) : (nb073_alpha_dummy_016 x y) ∈ (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_017 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0099 (x : Var) (y : Var) : (nb073_alpha_dummy_016 x y) ∈ (((syn_ccompl (Class.cab (nb073_alpha_dummy_082 x y) (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb073_alpha_dummy_082 x y) (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0100 : (nb073_alpha_dummy_014) ∈ (((Class.cab (nb073_alpha_dummy_080) (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014)) (Wff.classEq (Class.cv (nb073_alpha_dummy_080)) (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_080) (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014)) (Wff.classEq (Class.cv (nb073_alpha_dummy_080)) (syn_cphi (Class.cv (nb073_alpha_dummy_081))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0096) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0101 (x : Var) (y : Var) : (nb073_alpha_dummy_016 x y) ∈ (((Class.cab (nb073_alpha_dummy_082 x y) (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_082 x y) (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0098 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0102 : (nb073_alpha_dummy_081) ∈ (((Class.cv (nb073_alpha_dummy_081))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0103 (x : Var) (y : Var) : (nb073_alpha_dummy_083 x y) ∈ (((Class.cv (nb073_alpha_dummy_083 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0104 : (nb073_alpha_dummy_088) ∈ (((Wff.classMem (Class.cv (nb073_alpha_dummy_088)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb073_alpha_dummy_088)) (syn_c1c))).fv ∪ ((Class.cv (nb073_alpha_dummy_088))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0105 (x : Var) (y : Var) : (nb073_alpha_dummy_090 x y) ∈ (((Wff.classMem (Class.cv (nb073_alpha_dummy_090 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb073_alpha_dummy_090 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb073_alpha_dummy_090 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0106 : (nb073_alpha_dummy_088) ∈ (((Class.cv (nb073_alpha_dummy_088))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0107 (x : Var) (y : Var) : (nb073_alpha_dummy_090 x y) ∈ (((Class.cv (nb073_alpha_dummy_090 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0108 : (nb073_alpha_dummy_095) ∈ (((syn_cnin (Class.cv (nb073_alpha_dummy_095)) (Class.cv (nb073_alpha_dummy_096)))).fv ∪ ((syn_cnin (Class.cv (nb073_alpha_dummy_095)) (Class.cv (nb073_alpha_dummy_096)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0109 (x : Var) (y : Var) : (nb073_alpha_dummy_098 x y) ∈ (((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y)) (Class.cv (nb073_alpha_dummy_099 x y)))).fv ∪ ((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y)) (Class.cv (nb073_alpha_dummy_099 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0110 : (nb073_alpha_dummy_095) ∈ (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0111 (x : Var) (y : Var) : (nb073_alpha_dummy_098 x y) ∈ (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_099 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0112 : (nb073_alpha_dummy_096) ∈ (((syn_cnin (Class.cv (nb073_alpha_dummy_095)) (Class.cv (nb073_alpha_dummy_096)))).fv ∪ ((syn_cnin (Class.cv (nb073_alpha_dummy_095)) (Class.cv (nb073_alpha_dummy_096)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0113 (x : Var) (y : Var) : (nb073_alpha_dummy_099 x y) ∈ (((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y)) (Class.cv (nb073_alpha_dummy_099 x y)))).fv ∪ ((syn_cnin (Class.cv (nb073_alpha_dummy_098 x y)) (Class.cv (nb073_alpha_dummy_099 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0114 : (nb073_alpha_dummy_096) ∈ (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0115 (x : Var) (y : Var) : (nb073_alpha_dummy_099 x y) ∈ (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_099 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0116 : (nb073_alpha_dummy_095) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_095)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_096)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0117 (x : Var) (y : Var) : (nb073_alpha_dummy_098 x y) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_098 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_099 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0118 : (nb073_alpha_dummy_095) ∈ (((Class.cv (nb073_alpha_dummy_095))).fv ∪ ((Class.cv (nb073_alpha_dummy_095))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0119 (x : Var) (y : Var) : (nb073_alpha_dummy_098 x y) ∈ (((Class.cv (nb073_alpha_dummy_098 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_098 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0120 : (nb073_alpha_dummy_096) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_095)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_096)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0121 (x : Var) (y : Var) : (nb073_alpha_dummy_099 x y) ∈ (((syn_ccompl (Class.cv (nb073_alpha_dummy_098 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb073_alpha_dummy_099 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0122 : (nb073_alpha_dummy_096) ∈ (((Class.cv (nb073_alpha_dummy_096))).fv ∪ ((Class.cv (nb073_alpha_dummy_096))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0123 (x : Var) (y : Var) : (nb073_alpha_dummy_099 x y) ∈ (((Class.cv (nb073_alpha_dummy_099 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_099 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0124 : (nb073_alpha_dummy_015) ∈ (((Class.cv (nb073_alpha_dummy_014))).fv ∪ ((Class.cv (nb073_alpha_dummy_015))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0125 : (nb073_alpha_dummy_015) ∈ (((syn_ccompl (Class.cab (nb073_alpha_dummy_080) (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_014)) (Wff.classEq (Class.cv (nb073_alpha_dummy_080)) (syn_cphi (Class.cv (nb073_alpha_dummy_081)))))))).fv ∪ ((syn_ccompl (Class.cab (nb073_alpha_dummy_080) (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015)) (Wff.classEq (Class.cv (nb073_alpha_dummy_080)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0126 (x : Var) (y : Var) : (nb073_alpha_dummy_017 x y) ∈ (((Class.cv (nb073_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb073_alpha_dummy_017 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0127 (x : Var) (y : Var) : (nb073_alpha_dummy_017 x y) ∈ (((syn_ccompl (Class.cab (nb073_alpha_dummy_082 x y) (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y)) (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb073_alpha_dummy_082 x y) (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0128 : (nb073_alpha_dummy_015) ∈ (((Class.cab (nb073_alpha_dummy_080) (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015)) (Wff.classEq (Class.cv (nb073_alpha_dummy_080)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_080) (syn_wrex (nb073_alpha_dummy_081) (Class.cv (nb073_alpha_dummy_015)) (Wff.classEq (Class.cv (nb073_alpha_dummy_080)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_081))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0124) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0129 (x : Var) (y : Var) : (nb073_alpha_dummy_017 x y) ∈ (((Class.cab (nb073_alpha_dummy_082 x y) (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb073_alpha_dummy_082 x y) (syn_wrex (nb073_alpha_dummy_083 x y) (Class.cv (nb073_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb073_alpha_dummy_082 x y)) (syn_cun (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0126 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb073_support_mem_0130 : (nb073_alpha_dummy_081) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_081))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0131 (x : Var) (y : Var) : (nb073_alpha_dummy_083 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_083 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0132 : (nb073_alpha_dummy_081) ∈ (((syn_cphi (Class.cv (nb073_alpha_dummy_081)))).fv ∪ ((syn_cphi (Class.cv (nb073_alpha_dummy_081)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0133 (x : Var) (y : Var) : (nb073_alpha_dummy_083 x y) ∈ (((syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))).fv ∪ ((syn_cphi (Class.cv (nb073_alpha_dummy_083 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0134 : (nb073_alpha_dummy_000) ∈ (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014)) (Class.cv (nb073_alpha_dummy_000))) (Wff.classMem (Class.cv (nb073_alpha_dummy_015)) (Class.cv (nb073_alpha_dummy_001))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wa]
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0135 (x : Var) (y : Var) : x ∈ (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x)) (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wa]
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0136 : (nb073_alpha_dummy_001) ∈ (({(nb073_alpha_dummy_014)} : Finset Var) ∪ ({(nb073_alpha_dummy_015)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_014)) (Class.cv (nb073_alpha_dummy_000))) (Wff.classMem (Class.cv (nb073_alpha_dummy_015)) (Class.cv (nb073_alpha_dummy_001))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wa]
  apply Finset.mem_union_right
  rw [fv_wff_classMem]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_support_mem_0137 (x : Var) (y : Var) : y ∈ (({(nb073_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb073_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb073_alpha_dummy_016 x y)) (Class.cv x)) (Wff.classMem (Class.cv (nb073_alpha_dummy_017 x y)) (Class.cv y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wa]
  apply Finset.mem_union_right
  rw [fv_wff_classMem]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb073_compact_fv_empty_0000 : (nb073_alpha_dummy_030) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0000 : (nb073_alpha_dummy_030) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_030, fv_syn_c1c] using (nb073_compact_fv_empty_0000)

theorem nb073_compact_fv_empty_0001 (x : Var) (y : Var) : (nb073_alpha_dummy_033 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0001 (x : Var) (y : Var) : (nb073_alpha_dummy_033 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_033, fv_syn_c1c] using (nb073_compact_fv_empty_0001 x y)

theorem nb073_compact_fv_empty_0002 : (nb073_alpha_dummy_029) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0002 : (nb073_alpha_dummy_029) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_029, fv_syn_c1c] using (nb073_compact_fv_empty_0002)

theorem nb073_compact_fv_empty_0003 (x : Var) (y : Var) : (nb073_alpha_dummy_032 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0003 (x : Var) (y : Var) : (nb073_alpha_dummy_032 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_032, fv_syn_c1c] using (nb073_compact_fv_empty_0003 x y)

theorem nb073_compact_fv_empty_0004 : (nb073_alpha_dummy_028) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0004 : (nb073_alpha_dummy_028) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_028, fv_syn_c1c] using (nb073_compact_fv_empty_0004)

theorem nb073_compact_fv_empty_0005 (x : Var) (y : Var) : (nb073_alpha_dummy_031 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0005 (x : Var) (y : Var) : (nb073_alpha_dummy_031 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_031, fv_syn_c1c] using (nb073_compact_fv_empty_0005 x y)

theorem nb073_compact_fv_empty_0006 : (nb073_alpha_dummy_026) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0006 : (nb073_alpha_dummy_026) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_026, fv_syn_c1c] using (nb073_compact_fv_empty_0006)

theorem nb073_compact_fv_empty_0007 (x : Var) (y : Var) : (nb073_alpha_dummy_027 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0007 (x : Var) (y : Var) : (nb073_alpha_dummy_027 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_027, fv_syn_c1c] using (nb073_compact_fv_empty_0007 x y)

theorem nb073_compact_fv_empty_0008 : (nb073_alpha_dummy_022) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0008 : (nb073_alpha_dummy_022) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_022, fv_syn_c1c] using (nb073_compact_fv_empty_0008)

theorem nb073_compact_fv_empty_0009 (x : Var) (y : Var) : (nb073_alpha_dummy_024 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0009 (x : Var) (y : Var) : (nb073_alpha_dummy_024 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_024, fv_syn_c1c] using (nb073_compact_fv_empty_0009 x y)

theorem nb073_compact_fv_empty_0010 : (nb073_alpha_dummy_023) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0010 : (nb073_alpha_dummy_023) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_023, fv_syn_c1c] using (nb073_compact_fv_empty_0010)

theorem nb073_compact_fv_empty_0011 (x : Var) (y : Var) : (nb073_alpha_dummy_025 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0011 (x : Var) (y : Var) : (nb073_alpha_dummy_025 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_025, fv_syn_c1c] using (nb073_compact_fv_empty_0011 x y)

theorem nb073_compact_fv_empty_0012 : (nb073_alpha_dummy_015) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0012 : (nb073_alpha_dummy_015) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_015, fv_syn_c1c] using (nb073_compact_fv_empty_0012)

theorem nb073_compact_fv_empty_0013 (x : Var) (y : Var) : (nb073_alpha_dummy_017 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0013 (x : Var) (y : Var) : (nb073_alpha_dummy_017 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_017, fv_syn_c1c] using (nb073_compact_fv_empty_0013 x y)

theorem nb073_compact_fv_empty_0014 : (nb073_alpha_dummy_014) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0014 : (nb073_alpha_dummy_014) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_014, fv_syn_c1c] using (nb073_compact_fv_empty_0014)

theorem nb073_compact_fv_empty_0015 (x : Var) (y : Var) : (nb073_alpha_dummy_016 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0015 (x : Var) (y : Var) : (nb073_alpha_dummy_016 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_016, fv_syn_c1c] using (nb073_compact_fv_empty_0015 x y)

theorem nb073_compact_fv_empty_0016 : (nb073_alpha_dummy_020) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0016 : (nb073_alpha_dummy_020) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_020, fv_syn_c1c] using (nb073_compact_fv_empty_0016)

theorem nb073_compact_fv_empty_0017 (x : Var) (y : Var) : (nb073_alpha_dummy_021 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0017 (x : Var) (y : Var) : (nb073_alpha_dummy_021 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_021, fv_syn_c1c] using (nb073_compact_fv_empty_0017 x y)

theorem nb073_compact_fv_empty_0018 : (nb073_alpha_dummy_018) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0018 : (nb073_alpha_dummy_018) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_018, fv_syn_c1c] using (nb073_compact_fv_empty_0018)

theorem nb073_compact_fv_empty_0019 (x : Var) (y : Var) : (nb073_alpha_dummy_019 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0019 (x : Var) (y : Var) : (nb073_alpha_dummy_019 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_019, fv_syn_c1c] using (nb073_compact_fv_empty_0019 x y)

theorem nb073_compact_fv_empty_0020 : (nb073_alpha_dummy_007) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0020 : (nb073_alpha_dummy_007) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_007, fv_syn_c1c] using (nb073_compact_fv_empty_0020)

theorem nb073_compact_fv_empty_0021 (x : Var) (y : Var) : (nb073_alpha_dummy_009 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb073_wpp_notmem_0021 (x : Var) (y : Var) : (nb073_alpha_dummy_009 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb073_alpha_dummy_009, fv_syn_c1c] using (nb073_compact_fv_empty_0021 x y)

theorem nb073_compact_fv_empty_0022 : (nb073_alpha_dummy_006) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
