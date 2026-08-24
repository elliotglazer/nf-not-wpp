import NAR4C067C001Part007

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

theorem nb067_support_mem_0178 (f : Var) : (nb067_alpha_dummy_165 f) ∈ (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0179 (f : Var) : (nb067_alpha_dummy_165 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0180 : (nb067_alpha_dummy_163) ∈ (((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0181 (f : Var) : (nb067_alpha_dummy_165 f) ∈ (((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0182 : (nb067_alpha_dummy_170) ∈ (((Class.cv (nb067_alpha_dummy_170))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0183 (f : Var) : (nb067_alpha_dummy_172 f) ∈ (((Class.cv (nb067_alpha_dummy_172 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0184 : (nb067_alpha_dummy_177) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_177))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0185 (f : Var) : (nb067_alpha_dummy_179 f) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_179 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0186 : (nb067_alpha_dummy_177) ∈ (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0187 (f : Var) : (nb067_alpha_dummy_179 f) ∈ (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0188 : (nb067_alpha_dummy_184) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0189 (f : Var) : (nb067_alpha_dummy_187 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0190 : (nb067_alpha_dummy_184) ∈ (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0191 (f : Var) : (nb067_alpha_dummy_187 f) ∈ (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0192 : (nb067_alpha_dummy_185) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0193 (f : Var) : (nb067_alpha_dummy_188 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0194 : (nb067_alpha_dummy_185) ∈ (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0195 (f : Var) : (nb067_alpha_dummy_188 f) ∈ (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0196 : (nb067_alpha_dummy_184) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_184)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_185)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0197 (f : Var) : (nb067_alpha_dummy_187 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_187 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_188 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0198 : (nb067_alpha_dummy_184) ∈ (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_184))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0199 (f : Var) : (nb067_alpha_dummy_187 f) ∈ (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_187 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0200 : (nb067_alpha_dummy_185) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_184)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_185)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0201 (f : Var) : (nb067_alpha_dummy_188 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_187 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_188 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0202 : (nb067_alpha_dummy_185) ∈ (((Class.cv (nb067_alpha_dummy_185))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0203 (f : Var) : (nb067_alpha_dummy_188 f) ∈ (((Class.cv (nb067_alpha_dummy_188 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0204 : (nb067_alpha_dummy_164) ∈ (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0205 : (nb067_alpha_dummy_164) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0206 (f : Var) : (nb067_alpha_dummy_166 f) ∈ (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0207 (f : Var) : (nb067_alpha_dummy_166 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0208 : (nb067_alpha_dummy_164) ∈ (((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0209 (f : Var) : (nb067_alpha_dummy_166 f) ∈ (((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0210 : (nb067_alpha_dummy_170) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_170))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0211 (f : Var) : (nb067_alpha_dummy_172 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0212 : (nb067_alpha_dummy_170) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0213 (f : Var) : (nb067_alpha_dummy_172 f) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0214 : (nb067_alpha_dummy_164) ∈ (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0215 : (nb067_alpha_dummy_164) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0216 (f : Var) : (nb067_alpha_dummy_166 f) ∈ (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0217 (f : Var) : (nb067_alpha_dummy_166 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0218 : (nb067_alpha_dummy_164) ∈ (((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0219 (f : Var) : (nb067_alpha_dummy_166 f) ∈ (((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0220 : (nb067_alpha_dummy_206) ∈ (((Class.cv (nb067_alpha_dummy_206))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0221 (f : Var) : (nb067_alpha_dummy_208 f) ∈ (((Class.cv (nb067_alpha_dummy_208 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0222 : (nb067_alpha_dummy_213) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_213))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0223 (f : Var) : (nb067_alpha_dummy_215 f) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_215 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0224 : (nb067_alpha_dummy_213) ∈ (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0225 (f : Var) : (nb067_alpha_dummy_215 f) ∈ (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0226 : (nb067_alpha_dummy_220) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0227 (f : Var) : (nb067_alpha_dummy_223 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0228 : (nb067_alpha_dummy_220) ∈ (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0229 (f : Var) : (nb067_alpha_dummy_223 f) ∈ (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0230 : (nb067_alpha_dummy_221) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0231 (f : Var) : (nb067_alpha_dummy_224 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0232 : (nb067_alpha_dummy_221) ∈ (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0233 (f : Var) : (nb067_alpha_dummy_224 f) ∈ (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0234 : (nb067_alpha_dummy_220) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_220)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_221)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0235 (f : Var) : (nb067_alpha_dummy_223 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_223 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_224 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0236 : (nb067_alpha_dummy_220) ∈ (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_220))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0237 (f : Var) : (nb067_alpha_dummy_223 f) ∈ (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_223 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0238 : (nb067_alpha_dummy_221) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_220)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_221)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0239 (f : Var) : (nb067_alpha_dummy_224 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_223 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_224 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0240 : (nb067_alpha_dummy_221) ∈ (((Class.cv (nb067_alpha_dummy_221))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0241 (f : Var) : (nb067_alpha_dummy_224 f) ∈ (((Class.cv (nb067_alpha_dummy_224 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0242 : (nb067_alpha_dummy_163) ∈ (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0243 : (nb067_alpha_dummy_163) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0244 (f : Var) : (nb067_alpha_dummy_165 f) ∈ (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0245 (f : Var) : (nb067_alpha_dummy_165 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0246 : (nb067_alpha_dummy_163) ∈ (((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0247 (f : Var) : (nb067_alpha_dummy_165 f) ∈ (((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0248 : (nb067_alpha_dummy_206) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_206))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0249 (f : Var) : (nb067_alpha_dummy_208 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0250 : (nb067_alpha_dummy_206) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0251 (f : Var) : (nb067_alpha_dummy_208 f) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0252 : (nb067_alpha_dummy_000) ∈ (((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0253 (f : Var) : f ∈ (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0254 : (nb067_alpha_dummy_000) ∈ (((syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0255 (f : Var) : f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0256 : (nb067_alpha_dummy_000) ∈ (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0257 : (nb067_alpha_dummy_000) ∈ (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb067_support_mem_0258 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0259 (f : Var) : f ∈ (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb067_alpha_dummy_088 f))) (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_087 f)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb067_support_mem_0260 : (nb067_alpha_dummy_000) ∈ (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_163)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0261 (f : Var) : f ∈ (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_165 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0262 : (nb067_alpha_dummy_000) ∈ (((Class.cv (nb067_alpha_dummy_000))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0263 (f : Var) : f ∈ (((Class.cv f)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0264 : (nb067_alpha_dummy_085) ∈ (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0265 : (nb067_alpha_dummy_085) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0266 (f : Var) : (nb067_alpha_dummy_088 f) ∈ (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0267 (f : Var) : (nb067_alpha_dummy_088 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0268 : (nb067_alpha_dummy_085) ∈ (((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0269 (f : Var) : (nb067_alpha_dummy_088 f) ∈ (((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0270 : (nb067_alpha_dummy_242) ∈ (((Class.cv (nb067_alpha_dummy_242))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0271 (f : Var) : (nb067_alpha_dummy_244 f) ∈ (((Class.cv (nb067_alpha_dummy_244 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0272 : (nb067_alpha_dummy_249) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_249))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0273 (f : Var) : (nb067_alpha_dummy_251 f) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_251 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0274 : (nb067_alpha_dummy_249) ∈ (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0275 (f : Var) : (nb067_alpha_dummy_251 f) ∈ (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0276 : (nb067_alpha_dummy_256) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0277 (f : Var) : (nb067_alpha_dummy_259 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0278 : (nb067_alpha_dummy_256) ∈ (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0279 (f : Var) : (nb067_alpha_dummy_259 f) ∈ (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0280 : (nb067_alpha_dummy_257) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0281 (f : Var) : (nb067_alpha_dummy_260 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0282 : (nb067_alpha_dummy_257) ∈ (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0283 (f : Var) : (nb067_alpha_dummy_260 f) ∈ (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0284 : (nb067_alpha_dummy_256) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_256)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_257)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0285 (f : Var) : (nb067_alpha_dummy_259 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_259 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_260 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0286 : (nb067_alpha_dummy_256) ∈ (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_256))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0287 (f : Var) : (nb067_alpha_dummy_259 f) ∈ (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_259 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0288 : (nb067_alpha_dummy_257) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_256)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_257)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0289 (f : Var) : (nb067_alpha_dummy_260 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_259 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_260 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0290 : (nb067_alpha_dummy_257) ∈ (((Class.cv (nb067_alpha_dummy_257))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0291 (f : Var) : (nb067_alpha_dummy_260 f) ∈ (((Class.cv (nb067_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0292 : (nb067_alpha_dummy_084) ∈ (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0293 : (nb067_alpha_dummy_084) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0294 (f : Var) : (nb067_alpha_dummy_087 f) ∈ (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0295 (f : Var) : (nb067_alpha_dummy_087 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0296 : (nb067_alpha_dummy_084) ∈ (((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0297 (f : Var) : (nb067_alpha_dummy_087 f) ∈ (((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0298 : (nb067_alpha_dummy_242) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_242))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0299 (f : Var) : (nb067_alpha_dummy_244 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0300 : (nb067_alpha_dummy_242) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0301 (f : Var) : (nb067_alpha_dummy_244 f) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0302 : (nb067_alpha_dummy_278) ∈ (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0303 : (nb067_alpha_dummy_278) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0304 (f : Var) : (nb067_alpha_dummy_280 f) ∈ (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0305 (f : Var) : (nb067_alpha_dummy_280 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0306 : (nb067_alpha_dummy_278) ∈ (((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0307 (f : Var) : (nb067_alpha_dummy_280 f) ∈ (((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0308 : (nb067_alpha_dummy_282) ∈ (((Class.cv (nb067_alpha_dummy_282))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0309 (f : Var) : (nb067_alpha_dummy_284 f) ∈ (((Class.cv (nb067_alpha_dummy_284 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0310 : (nb067_alpha_dummy_289) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_289)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_289)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_289))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0311 (f : Var) : (nb067_alpha_dummy_291 f) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_291 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_291 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_291 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0312 : (nb067_alpha_dummy_289) ∈ (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0313 (f : Var) : (nb067_alpha_dummy_291 f) ∈ (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0314 : (nb067_alpha_dummy_296) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0315 (f : Var) : (nb067_alpha_dummy_299 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0316 : (nb067_alpha_dummy_296) ∈ (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0317 (f : Var) : (nb067_alpha_dummy_299 f) ∈ (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0318 : (nb067_alpha_dummy_297) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0319 (f : Var) : (nb067_alpha_dummy_300 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
