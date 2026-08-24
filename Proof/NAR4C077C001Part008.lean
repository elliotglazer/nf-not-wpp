import NAR4C077C001Part007

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

theorem nb077_support_mem_0165 (x : Var) : (nb077_alpha_dummy_143 x) ∈ (((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0162 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0166 (F : Class) (I : Class) : (nb077_alpha_dummy_148 F I) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0167 (x : Var) : (nb077_alpha_dummy_150 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0168 (F : Class) (I : Class) : (nb077_alpha_dummy_148 F I) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0169 (x : Var) : (nb077_alpha_dummy_150 x) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0170 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∈ (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_141 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0171 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0172 (x : Var) : (nb077_alpha_dummy_142 x) ∈ (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0173 (x : Var) : (nb077_alpha_dummy_142 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0174 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∈ (((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0170 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0175 (x : Var) : (nb077_alpha_dummy_142 x) ∈ (((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0172 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0176 (F : Class) (I : Class) : (nb077_alpha_dummy_184 F I) ∈ (((Class.cv (nb077_alpha_dummy_184 F I))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0177 (x : Var) : (nb077_alpha_dummy_186 x) ∈ (((Class.cv (nb077_alpha_dummy_186 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0178 (F : Class) (I : Class) : (nb077_alpha_dummy_191 F I) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_191 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_191 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_191 F I))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0179 (x : Var) : (nb077_alpha_dummy_193 x) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_193 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_193 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_193 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0180 (F : Class) (I : Class) : (nb077_alpha_dummy_191 F I) ∈ (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0181 (x : Var) : (nb077_alpha_dummy_193 x) ∈ (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0182 (F : Class) (I : Class) : (nb077_alpha_dummy_198 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I)) (Class.cv (nb077_alpha_dummy_199 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I)) (Class.cv (nb077_alpha_dummy_199 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0183 (x : Var) : (nb077_alpha_dummy_201 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0184 (F : Class) (I : Class) : (nb077_alpha_dummy_198 F I) ∈ (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_199 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0185 (x : Var) : (nb077_alpha_dummy_201 x) ∈ (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0186 (F : Class) (I : Class) : (nb077_alpha_dummy_199 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I)) (Class.cv (nb077_alpha_dummy_199 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I)) (Class.cv (nb077_alpha_dummy_199 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0187 (x : Var) : (nb077_alpha_dummy_202 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0188 (F : Class) (I : Class) : (nb077_alpha_dummy_199 F I) ∈ (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_199 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0189 (x : Var) : (nb077_alpha_dummy_202 x) ∈ (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0190 (F : Class) (I : Class) : (nb077_alpha_dummy_198 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_198 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_199 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0191 (x : Var) : (nb077_alpha_dummy_201 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_201 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_202 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0192 (F : Class) (I : Class) : (nb077_alpha_dummy_198 F I) ∈ (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_198 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0193 (x : Var) : (nb077_alpha_dummy_201 x) ∈ (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_201 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0194 (F : Class) (I : Class) : (nb077_alpha_dummy_199 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_198 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_199 F I)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0195 (x : Var) : (nb077_alpha_dummy_202 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_201 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_202 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0196 (F : Class) (I : Class) : (nb077_alpha_dummy_199 F I) ∈ (((Class.cv (nb077_alpha_dummy_199 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_199 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0197 (x : Var) : (nb077_alpha_dummy_202 x) ∈ (((Class.cv (nb077_alpha_dummy_202 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0198 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∈ (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_141 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0199 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0200 (x : Var) : (nb077_alpha_dummy_144 x) ∈ (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0201 (x : Var) : (nb077_alpha_dummy_144 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0202 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∈ (((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0198 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0203 (x : Var) : (nb077_alpha_dummy_144 x) ∈ (((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0200 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0204 (F : Class) (I : Class) : (nb077_alpha_dummy_184 F I) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0205 (x : Var) : (nb077_alpha_dummy_186 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0206 (F : Class) (I : Class) : (nb077_alpha_dummy_184 F I) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0207 (x : Var) : (nb077_alpha_dummy_186 x) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0208 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∈ (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0209 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0210 (x : Var) : (nb077_alpha_dummy_144 x) ∈ (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0211 (x : Var) : (nb077_alpha_dummy_144 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0212 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∈ (((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0208 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0213 (x : Var) : (nb077_alpha_dummy_144 x) ∈ (((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0210 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0214 (F : Class) (I : Class) : (nb077_alpha_dummy_220 F I) ∈ (((Class.cv (nb077_alpha_dummy_220 F I))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0215 (x : Var) : (nb077_alpha_dummy_222 x) ∈ (((Class.cv (nb077_alpha_dummy_222 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0216 (F : Class) (I : Class) : (nb077_alpha_dummy_227 F I) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_227 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_227 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_227 F I))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0217 (x : Var) : (nb077_alpha_dummy_229 x) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_229 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_229 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_229 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0218 (F : Class) (I : Class) : (nb077_alpha_dummy_227 F I) ∈ (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0219 (x : Var) : (nb077_alpha_dummy_229 x) ∈ (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0220 (F : Class) (I : Class) : (nb077_alpha_dummy_234 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I)) (Class.cv (nb077_alpha_dummy_235 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I)) (Class.cv (nb077_alpha_dummy_235 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0221 (x : Var) : (nb077_alpha_dummy_237 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0222 (F : Class) (I : Class) : (nb077_alpha_dummy_234 F I) ∈ (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_235 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0223 (x : Var) : (nb077_alpha_dummy_237 x) ∈ (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0224 (F : Class) (I : Class) : (nb077_alpha_dummy_235 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I)) (Class.cv (nb077_alpha_dummy_235 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I)) (Class.cv (nb077_alpha_dummy_235 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0225 (x : Var) : (nb077_alpha_dummy_238 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0226 (F : Class) (I : Class) : (nb077_alpha_dummy_235 F I) ∈ (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_235 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0227 (x : Var) : (nb077_alpha_dummy_238 x) ∈ (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0228 (F : Class) (I : Class) : (nb077_alpha_dummy_234 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_234 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_235 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0229 (x : Var) : (nb077_alpha_dummy_237 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_237 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_238 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0230 (F : Class) (I : Class) : (nb077_alpha_dummy_234 F I) ∈ (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_234 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0231 (x : Var) : (nb077_alpha_dummy_237 x) ∈ (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_237 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0232 (F : Class) (I : Class) : (nb077_alpha_dummy_235 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_234 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_235 F I)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0233 (x : Var) : (nb077_alpha_dummy_238 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_237 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_238 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0234 (F : Class) (I : Class) : (nb077_alpha_dummy_235 F I) ∈ (((Class.cv (nb077_alpha_dummy_235 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_235 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0235 (x : Var) : (nb077_alpha_dummy_238 x) ∈ (((Class.cv (nb077_alpha_dummy_238 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0236 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∈ (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0237 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0238 (x : Var) : (nb077_alpha_dummy_143 x) ∈ (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0239 (x : Var) : (nb077_alpha_dummy_143 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0240 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∈ (((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0236 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0241 (x : Var) : (nb077_alpha_dummy_143 x) ∈ (((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0238 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0242 (F : Class) (I : Class) : (nb077_alpha_dummy_220 F I) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0243 (x : Var) : (nb077_alpha_dummy_222 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0244 (F : Class) (I : Class) : (nb077_alpha_dummy_220 F I) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0245 (x : Var) : (nb077_alpha_dummy_222 x) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0246 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∈ (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_255 F I)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb077_alpha_dummy_000 F I)) (syn_cvv)) (Wff.classEq (Class.cv (nb077_alpha_dummy_255 F I)) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0247 (x : Var) : x ∈ (({x} : Finset Var) ∪ ({(nb077_alpha_dummy_256 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb077_alpha_dummy_256 x)) (syn_cplc (Class.cv x) (syn_c1c))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0248 (F : Class) (I : Class) : (nb077_alpha_dummy_255 F I) ∈ (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_255 F I)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb077_alpha_dummy_000 F I)) (syn_cvv)) (Wff.classEq (Class.cv (nb077_alpha_dummy_255 F I)) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0249 (x : Var) : (nb077_alpha_dummy_256 x) ∈ (({x} : Finset Var) ∪ ({(nb077_alpha_dummy_256 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb077_alpha_dummy_256 x)) (syn_cplc (Class.cv x) (syn_c1c))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0250 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∈ (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0251 (x : Var) : x ∈ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (syn_c1c))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0252 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∈ (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_255 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0253 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0254 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0255 (x : Var) : x ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0256 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∈ (((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0252 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0257 (x : Var) : x ∈ (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0254 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0258 (F : Class) (I : Class) : (nb077_alpha_dummy_260 F I) ∈ (((Class.cv (nb077_alpha_dummy_260 F I))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0259 (x : Var) : (nb077_alpha_dummy_262 x) ∈ (((Class.cv (nb077_alpha_dummy_262 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0260 (F : Class) (I : Class) : (nb077_alpha_dummy_267 F I) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_267 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_267 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_267 F I))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0261 (x : Var) : (nb077_alpha_dummy_269 x) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_269 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_269 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_269 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0262 (F : Class) (I : Class) : (nb077_alpha_dummy_267 F I) ∈ (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0263 (x : Var) : (nb077_alpha_dummy_269 x) ∈ (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0264 (F : Class) (I : Class) : (nb077_alpha_dummy_274 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I)) (Class.cv (nb077_alpha_dummy_275 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I)) (Class.cv (nb077_alpha_dummy_275 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0265 (x : Var) : (nb077_alpha_dummy_277 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0266 (F : Class) (I : Class) : (nb077_alpha_dummy_274 F I) ∈ (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_275 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0267 (x : Var) : (nb077_alpha_dummy_277 x) ∈ (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0268 (F : Class) (I : Class) : (nb077_alpha_dummy_275 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I)) (Class.cv (nb077_alpha_dummy_275 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I)) (Class.cv (nb077_alpha_dummy_275 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0269 (x : Var) : (nb077_alpha_dummy_278 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0270 (F : Class) (I : Class) : (nb077_alpha_dummy_275 F I) ∈ (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_275 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0271 (x : Var) : (nb077_alpha_dummy_278 x) ∈ (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0272 (F : Class) (I : Class) : (nb077_alpha_dummy_274 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_274 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_275 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0273 (x : Var) : (nb077_alpha_dummy_277 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_277 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_278 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0274 (F : Class) (I : Class) : (nb077_alpha_dummy_274 F I) ∈ (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_274 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0275 (x : Var) : (nb077_alpha_dummy_277 x) ∈ (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_277 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0276 (F : Class) (I : Class) : (nb077_alpha_dummy_275 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_274 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_275 F I)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0277 (x : Var) : (nb077_alpha_dummy_278 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_277 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_278 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0278 (F : Class) (I : Class) : (nb077_alpha_dummy_275 F I) ∈ (((Class.cv (nb077_alpha_dummy_275 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_275 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0279 (x : Var) : (nb077_alpha_dummy_278 x) ∈ (((Class.cv (nb077_alpha_dummy_278 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0280 (F : Class) (I : Class) : (nb077_alpha_dummy_255 F I) ∈ (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_255 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0281 (F : Class) (I : Class) : (nb077_alpha_dummy_255 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0282 (x : Var) : (nb077_alpha_dummy_256 x) ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0283 (x : Var) : (nb077_alpha_dummy_256 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0284 (F : Class) (I : Class) : (nb077_alpha_dummy_255 F I) ∈ (((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0280 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0285 (x : Var) : (nb077_alpha_dummy_256 x) ∈ (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0282 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0286 (F : Class) (I : Class) : (nb077_alpha_dummy_260 F I) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0287 (x : Var) : (nb077_alpha_dummy_262 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0288 (F : Class) (I : Class) : (nb077_alpha_dummy_260 F I) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0289 (x : Var) : (nb077_alpha_dummy_262 x) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0290 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∈ (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0291 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0292 (F : Class) (I : Class) : (nb077_alpha_dummy_296 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I)) (Class.cv (nb077_alpha_dummy_297 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I)) (Class.cv (nb077_alpha_dummy_297 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0293 (x : Var) : (nb077_alpha_dummy_299 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0294 (F : Class) (I : Class) : (nb077_alpha_dummy_296 F I) ∈ (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_297 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0295 (x : Var) : (nb077_alpha_dummy_299 x) ∈ (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0296 (F : Class) (I : Class) : (nb077_alpha_dummy_297 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I)) (Class.cv (nb077_alpha_dummy_297 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I)) (Class.cv (nb077_alpha_dummy_297 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0297 (x : Var) : (nb077_alpha_dummy_300 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0298 (F : Class) (I : Class) : (nb077_alpha_dummy_297 F I) ∈ (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_297 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0299 (x : Var) : (nb077_alpha_dummy_300 x) ∈ (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0300 (F : Class) (I : Class) : (nb077_alpha_dummy_296 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_296 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_297 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0301 (x : Var) : (nb077_alpha_dummy_299 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_299 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_300 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0302 (F : Class) (I : Class) : (nb077_alpha_dummy_296 F I) ∈ (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_296 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0303 (x : Var) : (nb077_alpha_dummy_299 x) ∈ (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_299 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
