import NAR4C055C001Part004

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

theorem nb055_support_mem_0138 : (nb055_alpha_dummy_014) ∈ (((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0134) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0134) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0139 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∈ (((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0136 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0136 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0140 : (nb055_alpha_dummy_119) ∈ (((Class.cv (nb055_alpha_dummy_119))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0141 (x : Var) (y : Var) : (nb055_alpha_dummy_121 x y) ∈ (((Class.cv (nb055_alpha_dummy_121 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0142 : (nb055_alpha_dummy_126) ∈ (((Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_126)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_126))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0143 (x : Var) (y : Var) : (nb055_alpha_dummy_128 x y) ∈ (((Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_128 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_128 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0144 : (nb055_alpha_dummy_126) ∈ (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0145 (x : Var) (y : Var) : (nb055_alpha_dummy_128 x y) ∈ (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0146 : (nb055_alpha_dummy_133) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0147 (x : Var) (y : Var) : (nb055_alpha_dummy_136 x y) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0148 : (nb055_alpha_dummy_133) ∈ (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0149 (x : Var) (y : Var) : (nb055_alpha_dummy_136 x y) ∈ (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_137 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0150 : (nb055_alpha_dummy_134) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0151 (x : Var) (y : Var) : (nb055_alpha_dummy_137 x y) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0152 : (nb055_alpha_dummy_134) ∈ (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0153 (x : Var) (y : Var) : (nb055_alpha_dummy_137 x y) ∈ (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_137 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0154 : (nb055_alpha_dummy_133) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_133)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_134)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0155 (x : Var) (y : Var) : (nb055_alpha_dummy_136 x y) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_136 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_137 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0156 : (nb055_alpha_dummy_133) ∈ (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_133))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0157 (x : Var) (y : Var) : (nb055_alpha_dummy_136 x y) ∈ (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_136 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0158 : (nb055_alpha_dummy_134) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_133)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_134)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0159 (x : Var) (y : Var) : (nb055_alpha_dummy_137 x y) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_136 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_137 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0160 : (nb055_alpha_dummy_134) ∈ (((Class.cv (nb055_alpha_dummy_134))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0161 (x : Var) (y : Var) : (nb055_alpha_dummy_137 x y) ∈ (((Class.cv (nb055_alpha_dummy_137 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_137 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0162 : (nb055_alpha_dummy_078) ∈ (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0163 : (nb055_alpha_dummy_078) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0164 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∈ (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_079 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0165 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0166 : (nb055_alpha_dummy_078) ∈ (((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0167 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∈ (((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0168 : (nb055_alpha_dummy_119) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_119))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0169 (x : Var) (y : Var) : (nb055_alpha_dummy_121 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0170 : (nb055_alpha_dummy_119) ∈ (((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0171 (x : Var) (y : Var) : (nb055_alpha_dummy_121 x y) ∈ (((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0172 : (nb055_alpha_dummy_001) ∈ (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014)) (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078))) (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_015)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb055_support_mem_0173 (x : Var) (y : Var) : y ∈ (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y) (Class.cv (nb055_alpha_dummy_079 x y))) (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x) (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb055_support_mem_0174 : (nb055_alpha_dummy_078) ∈ (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0175 : (nb055_alpha_dummy_078) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0174) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0174) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0176 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∈ (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0177 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0176 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0176 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0178 : (nb055_alpha_dummy_078) ∈ (((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0174) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0174) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0179 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∈ (((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0176 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0176 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0180 : (nb055_alpha_dummy_155) ∈ (((Class.cv (nb055_alpha_dummy_155))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0181 (x : Var) (y : Var) : (nb055_alpha_dummy_157 x y) ∈ (((Class.cv (nb055_alpha_dummy_157 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0182 : (nb055_alpha_dummy_162) ∈ (((Wff.classMem (Class.cv (nb055_alpha_dummy_162)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_162)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_162))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0183 (x : Var) (y : Var) : (nb055_alpha_dummy_164 x y) ∈ (((Wff.classMem (Class.cv (nb055_alpha_dummy_164 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_164 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_164 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0184 : (nb055_alpha_dummy_162) ∈ (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0185 (x : Var) (y : Var) : (nb055_alpha_dummy_164 x y) ∈ (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0186 : (nb055_alpha_dummy_169) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0187 (x : Var) (y : Var) : (nb055_alpha_dummy_172 x y) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0188 : (nb055_alpha_dummy_169) ∈ (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0189 (x : Var) (y : Var) : (nb055_alpha_dummy_172 x y) ∈ (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_173 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0190 : (nb055_alpha_dummy_170) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0191 (x : Var) (y : Var) : (nb055_alpha_dummy_173 x y) ∈ (((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0192 : (nb055_alpha_dummy_170) ∈ (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0193 (x : Var) (y : Var) : (nb055_alpha_dummy_173 x y) ∈ (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_173 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0194 : (nb055_alpha_dummy_169) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_169)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_170)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0195 (x : Var) (y : Var) : (nb055_alpha_dummy_172 x y) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_172 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_173 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0196 : (nb055_alpha_dummy_169) ∈ (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_169))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0197 (x : Var) (y : Var) : (nb055_alpha_dummy_172 x y) ∈ (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_172 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0198 : (nb055_alpha_dummy_170) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_169)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_170)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0199 (x : Var) (y : Var) : (nb055_alpha_dummy_173 x y) ∈ (((syn_ccompl (Class.cv (nb055_alpha_dummy_172 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_173 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0200 : (nb055_alpha_dummy_170) ∈ (((Class.cv (nb055_alpha_dummy_170))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0201 (x : Var) (y : Var) : (nb055_alpha_dummy_173 x y) ∈ (((Class.cv (nb055_alpha_dummy_173 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_173 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0202 : (nb055_alpha_dummy_015) ∈ (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0203 : (nb055_alpha_dummy_015) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0204 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∈ (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_017 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0205 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∈ (((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0206 : (nb055_alpha_dummy_015) ∈ (((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0207 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∈ (((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb055_support_mem_0208 : (nb055_alpha_dummy_155) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_155))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0209 (x : Var) (y : Var) : (nb055_alpha_dummy_157 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0210 : (nb055_alpha_dummy_155) ∈ (((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0211 (x : Var) (y : Var) : (nb055_alpha_dummy_157 x y) ∈ (((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0212 : (nb055_alpha_dummy_000) ∈ (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014)) (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078))) (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_015)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_right
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb055_support_mem_0213 (x : Var) (y : Var) : x ∈ (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y) (Class.cv (nb055_alpha_dummy_079 x y))) (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x) (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_right
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb055_compact_fv_empty_0000 : (nb055_alpha_dummy_030) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0000 : (nb055_alpha_dummy_030) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_030, fv_syn_c1c] using (nb055_compact_fv_empty_0000)

theorem nb055_compact_fv_empty_0001 (x : Var) (y : Var) : (nb055_alpha_dummy_033 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0001 (x : Var) (y : Var) : (nb055_alpha_dummy_033 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_033, fv_syn_c1c] using (nb055_compact_fv_empty_0001 x y)

theorem nb055_compact_fv_empty_0002 : (nb055_alpha_dummy_029) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0002 : (nb055_alpha_dummy_029) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_029, fv_syn_c1c] using (nb055_compact_fv_empty_0002)

theorem nb055_compact_fv_empty_0003 (x : Var) (y : Var) : (nb055_alpha_dummy_032 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0003 (x : Var) (y : Var) : (nb055_alpha_dummy_032 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_032, fv_syn_c1c] using (nb055_compact_fv_empty_0003 x y)

theorem nb055_compact_fv_empty_0004 : (nb055_alpha_dummy_028) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0004 : (nb055_alpha_dummy_028) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_028, fv_syn_c1c] using (nb055_compact_fv_empty_0004)

theorem nb055_compact_fv_empty_0005 (x : Var) (y : Var) : (nb055_alpha_dummy_031 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0005 (x : Var) (y : Var) : (nb055_alpha_dummy_031 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_031, fv_syn_c1c] using (nb055_compact_fv_empty_0005 x y)

theorem nb055_compact_fv_empty_0006 : (nb055_alpha_dummy_026) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0006 : (nb055_alpha_dummy_026) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_026, fv_syn_c1c] using (nb055_compact_fv_empty_0006)

theorem nb055_compact_fv_empty_0007 (x : Var) (y : Var) : (nb055_alpha_dummy_027 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0007 (x : Var) (y : Var) : (nb055_alpha_dummy_027 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_027, fv_syn_c1c] using (nb055_compact_fv_empty_0007 x y)

theorem nb055_compact_fv_empty_0008 : (nb055_alpha_dummy_022) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0008 : (nb055_alpha_dummy_022) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_022, fv_syn_c1c] using (nb055_compact_fv_empty_0008)

theorem nb055_compact_fv_empty_0009 (x : Var) (y : Var) : (nb055_alpha_dummy_024 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0009 (x : Var) (y : Var) : (nb055_alpha_dummy_024 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_024, fv_syn_c1c] using (nb055_compact_fv_empty_0009 x y)

theorem nb055_compact_fv_empty_0010 : (nb055_alpha_dummy_023) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0010 : (nb055_alpha_dummy_023) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_023, fv_syn_c1c] using (nb055_compact_fv_empty_0010)

theorem nb055_compact_fv_empty_0011 (x : Var) (y : Var) : (nb055_alpha_dummy_025 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0011 (x : Var) (y : Var) : (nb055_alpha_dummy_025 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_025, fv_syn_c1c] using (nb055_compact_fv_empty_0011 x y)

theorem nb055_compact_fv_empty_0012 : (nb055_alpha_dummy_015) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0012 : (nb055_alpha_dummy_015) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_015, fv_syn_c1c] using (nb055_compact_fv_empty_0012)

theorem nb055_compact_fv_empty_0013 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0013 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_017, fv_syn_c1c] using (nb055_compact_fv_empty_0013 x y)

theorem nb055_compact_fv_empty_0014 : (nb055_alpha_dummy_014) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0014 : (nb055_alpha_dummy_014) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_014, fv_syn_c1c] using (nb055_compact_fv_empty_0014)

theorem nb055_compact_fv_empty_0015 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0015 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_016, fv_syn_c1c] using (nb055_compact_fv_empty_0015 x y)

theorem nb055_compact_fv_empty_0016 : (nb055_alpha_dummy_020) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0016 : (nb055_alpha_dummy_020) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_020, fv_syn_c1c] using (nb055_compact_fv_empty_0016)

theorem nb055_compact_fv_empty_0017 (x : Var) (y : Var) : (nb055_alpha_dummy_021 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0017 (x : Var) (y : Var) : (nb055_alpha_dummy_021 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_021, fv_syn_c1c] using (nb055_compact_fv_empty_0017 x y)

theorem nb055_compact_fv_empty_0018 : (nb055_alpha_dummy_018) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0018 : (nb055_alpha_dummy_018) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_018, fv_syn_c1c] using (nb055_compact_fv_empty_0018)

theorem nb055_compact_fv_empty_0019 (x : Var) (y : Var) : (nb055_alpha_dummy_019 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0019 (x : Var) (y : Var) : (nb055_alpha_dummy_019 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_019, fv_syn_c1c] using (nb055_compact_fv_empty_0019 x y)

theorem nb055_compact_fv_empty_0020 : (nb055_alpha_dummy_007) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0020 : (nb055_alpha_dummy_007) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_007, fv_syn_c1c] using (nb055_compact_fv_empty_0020)

theorem nb055_compact_fv_empty_0021 (x : Var) (y : Var) : (nb055_alpha_dummy_009 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0021 (x : Var) (y : Var) : (nb055_alpha_dummy_009 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_009, fv_syn_c1c] using (nb055_compact_fv_empty_0021 x y)

theorem nb055_compact_fv_empty_0022 : (nb055_alpha_dummy_006) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0022 : (nb055_alpha_dummy_006) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_006, fv_syn_c1c] using (nb055_compact_fv_empty_0022)

theorem nb055_compact_fv_empty_0023 (x : Var) (y : Var) : (nb055_alpha_dummy_008 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0023 (x : Var) (y : Var) : (nb055_alpha_dummy_008 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_008, fv_syn_c1c] using (nb055_compact_fv_empty_0023 x y)

theorem nb055_compact_fv_empty_0024 : (nb055_alpha_dummy_012) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0024 : (nb055_alpha_dummy_012) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_012, fv_syn_c1c] using (nb055_compact_fv_empty_0024)

theorem nb055_compact_fv_empty_0025 (x : Var) (y : Var) : (nb055_alpha_dummy_013 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0025 (x : Var) (y : Var) : (nb055_alpha_dummy_013 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_013, fv_syn_c1c] using (nb055_compact_fv_empty_0025 x y)

theorem nb055_compact_fv_empty_0026 : (nb055_alpha_dummy_010) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0026 : (nb055_alpha_dummy_010) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_010, fv_syn_c1c] using (nb055_compact_fv_empty_0026)

theorem nb055_compact_fv_empty_0027 (x : Var) (y : Var) : (nb055_alpha_dummy_011 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0027 (x : Var) (y : Var) : (nb055_alpha_dummy_011 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_011, fv_syn_c1c] using (nb055_compact_fv_empty_0027 x y)

theorem nb055_compact_fv_empty_0028 : (nb055_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0028 : (nb055_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_002, fv_syn_c1c] using (nb055_compact_fv_empty_0028)

theorem nb055_compact_fv_empty_0029 (x : Var) (y : Var) : (nb055_alpha_dummy_003 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0029 (x : Var) (y : Var) : (nb055_alpha_dummy_003 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_003, fv_syn_c1c] using (nb055_compact_fv_empty_0029 x y)

theorem nb055_compact_fv_empty_0030 : (nb055_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0030 : (nb055_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_001, fv_syn_c1c] using (nb055_compact_fv_empty_0030)

theorem nb055_compact_fv_empty_0031 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0031 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb055_compact_fv_empty_0031 y)

theorem nb055_compact_fv_empty_0032 : (nb055_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0032 : (nb055_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_000, fv_syn_c1c] using (nb055_compact_fv_empty_0032)

theorem nb055_compact_fv_empty_0033 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0033 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb055_compact_fv_empty_0033 x)

theorem nb055_compact_fv_empty_0034 : (nb055_alpha_dummy_004) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0034 : (nb055_alpha_dummy_004) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_004, fv_syn_c1c] using (nb055_compact_fv_empty_0034)

theorem nb055_compact_fv_empty_0035 (x : Var) (y : Var) : (nb055_alpha_dummy_005 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0035 (x : Var) (y : Var) : (nb055_alpha_dummy_005 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_005, fv_syn_c1c] using (nb055_compact_fv_empty_0035 x y)

theorem nb055_compact_envfresh_0000 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_030), (nb055_alpha_dummy_033 x y)), ((nb055_alpha_dummy_029), (nb055_alpha_dummy_032 x y)), ((nb055_alpha_dummy_028), (nb055_alpha_dummy_031 x y)), ((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)), ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)), ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_020), (nb055_alpha_dummy_021 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_030) (nb055_alpha_dummy_033 x y) (nb055_wpp_notmem_0000) (nb055_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_029) (nb055_alpha_dummy_032 x y) (nb055_wpp_notmem_0002) (nb055_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_028) (nb055_alpha_dummy_031 x y) (nb055_wpp_notmem_0004) (nb055_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_026) (nb055_alpha_dummy_027 x y) (nb055_wpp_notmem_0006) (nb055_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_022) (nb055_alpha_dummy_024 x y) (nb055_wpp_notmem_0008) (nb055_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_023) (nb055_alpha_dummy_025 x y) (nb055_wpp_notmem_0010) (nb055_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0012) (nb055_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0014) (nb055_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_020) (nb055_alpha_dummy_021 x y) (nb055_wpp_notmem_0016) (nb055_wpp_notmem_0017 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_018) (nb055_alpha_dummy_019 x y) (nb055_wpp_notmem_0018) (nb055_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_007) (nb055_alpha_dummy_009 x y) (nb055_wpp_notmem_0020) (nb055_wpp_notmem_0021 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_006) (nb055_alpha_dummy_008 x y) (nb055_wpp_notmem_0022) (nb055_wpp_notmem_0023 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_012) (nb055_alpha_dummy_013 x y) (nb055_wpp_notmem_0024) (nb055_wpp_notmem_0025 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_010) (nb055_alpha_dummy_011 x y) (nb055_wpp_notmem_0026) (nb055_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0028) (nb055_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0030) (nb055_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0032) (nb055_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0034) (nb055_wpp_notmem_0035 x y) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb055_wpp_refl_0000 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_030), (nb055_alpha_dummy_033 x y)), ((nb055_alpha_dummy_029), (nb055_alpha_dummy_032 x y)), ((nb055_alpha_dummy_028), (nb055_alpha_dummy_031 x y)), ((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)), ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)), ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_020), (nb055_alpha_dummy_021 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0000 x y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
