import NAR4C090C001Part016

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

theorem nb090_support_mem_0217 (h : Var) : (nb090_alpha_dummy_054 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0218 (A : Class) : (nb090_alpha_dummy_051 A) ∈ (((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv) := by
  apply Finset.mem_union_left
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

theorem nb090_support_mem_0219 (h : Var) : (nb090_alpha_dummy_054 h) ∈ (((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0220 (A : Class) : (nb090_alpha_dummy_208 A) ∈ (((Class.cv (nb090_alpha_dummy_208 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0221 (h : Var) : (nb090_alpha_dummy_210 h) ∈ (((Class.cv (nb090_alpha_dummy_210 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0222 (A : Class) : (nb090_alpha_dummy_215 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_215 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_215 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_215 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0223 (h : Var) : (nb090_alpha_dummy_217 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_217 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_217 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_217 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0224 (A : Class) : (nb090_alpha_dummy_215 A) ∈ (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0225 (h : Var) : (nb090_alpha_dummy_217 h) ∈ (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0226 (A : Class) : (nb090_alpha_dummy_222 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0227 (h : Var) : (nb090_alpha_dummy_225 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0228 (A : Class) : (nb090_alpha_dummy_222 A) ∈ (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0229 (h : Var) : (nb090_alpha_dummy_225 h) ∈ (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0230 (A : Class) : (nb090_alpha_dummy_223 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0231 (h : Var) : (nb090_alpha_dummy_226 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0232 (A : Class) : (nb090_alpha_dummy_223 A) ∈ (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0233 (h : Var) : (nb090_alpha_dummy_226 h) ∈ (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0234 (A : Class) : (nb090_alpha_dummy_222 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_222 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_223 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0235 (h : Var) : (nb090_alpha_dummy_225 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_225 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_226 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0236 (A : Class) : (nb090_alpha_dummy_222 A) ∈ (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_222 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0237 (h : Var) : (nb090_alpha_dummy_225 h) ∈ (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_225 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0238 (A : Class) : (nb090_alpha_dummy_223 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_222 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_223 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0239 (h : Var) : (nb090_alpha_dummy_226 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_225 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_226 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0240 (A : Class) : (nb090_alpha_dummy_223 A) ∈ (((Class.cv (nb090_alpha_dummy_223 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0241 (h : Var) : (nb090_alpha_dummy_226 h) ∈ (((Class.cv (nb090_alpha_dummy_226 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0242 (A : Class) : (nb090_alpha_dummy_050 A) ∈ (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0243 (A : Class) : (nb090_alpha_dummy_050 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0244 (h : Var) : (nb090_alpha_dummy_053 h) ∈ (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0245 (h : Var) : (nb090_alpha_dummy_053 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0246 (A : Class) : (nb090_alpha_dummy_050 A) ∈ (((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0247 (h : Var) : (nb090_alpha_dummy_053 h) ∈ (((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0248 (A : Class) : (nb090_alpha_dummy_208 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0249 (h : Var) : (nb090_alpha_dummy_210 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0250 (A : Class) : (nb090_alpha_dummy_208 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0251 (h : Var) : (nb090_alpha_dummy_210 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0252 (A : Class) : (nb090_alpha_dummy_244 A) ∈ (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0253 (A : Class) : (nb090_alpha_dummy_244 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0254 (h : Var) : (nb090_alpha_dummy_246 h) ∈ (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0255 (h : Var) : (nb090_alpha_dummy_246 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0256 (A : Class) : (nb090_alpha_dummy_244 A) ∈ (((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0257 (h : Var) : (nb090_alpha_dummy_246 h) ∈ (((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0258 (A : Class) : (nb090_alpha_dummy_248 A) ∈ (((Class.cv (nb090_alpha_dummy_248 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0259 (h : Var) : (nb090_alpha_dummy_250 h) ∈ (((Class.cv (nb090_alpha_dummy_250 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0260 (A : Class) : (nb090_alpha_dummy_255 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_255 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_255 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_255 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0261 (h : Var) : (nb090_alpha_dummy_257 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_257 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_257 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_257 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0262 (A : Class) : (nb090_alpha_dummy_255 A) ∈ (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0263 (h : Var) : (nb090_alpha_dummy_257 h) ∈ (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0264 (A : Class) : (nb090_alpha_dummy_262 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0265 (h : Var) : (nb090_alpha_dummy_265 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0266 (A : Class) : (nb090_alpha_dummy_262 A) ∈ (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0267 (h : Var) : (nb090_alpha_dummy_265 h) ∈ (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0268 (A : Class) : (nb090_alpha_dummy_263 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0269 (h : Var) : (nb090_alpha_dummy_266 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0270 (A : Class) : (nb090_alpha_dummy_263 A) ∈ (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0271 (h : Var) : (nb090_alpha_dummy_266 h) ∈ (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0272 (A : Class) : (nb090_alpha_dummy_262 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_262 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_263 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0273 (h : Var) : (nb090_alpha_dummy_265 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_265 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_266 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0274 (A : Class) : (nb090_alpha_dummy_262 A) ∈ (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_262 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0275 (h : Var) : (nb090_alpha_dummy_265 h) ∈ (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_265 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0276 (A : Class) : (nb090_alpha_dummy_263 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_262 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_263 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0277 (h : Var) : (nb090_alpha_dummy_266 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_265 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_266 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0278 (A : Class) : (nb090_alpha_dummy_263 A) ∈ (((Class.cv (nb090_alpha_dummy_263 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0279 (h : Var) : (nb090_alpha_dummy_266 h) ∈ (((Class.cv (nb090_alpha_dummy_266 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0280 (A : Class) : (nb090_alpha_dummy_243 A) ∈ (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0281 (A : Class) : (nb090_alpha_dummy_243 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0282 (h : Var) : (nb090_alpha_dummy_245 h) ∈ (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0283 (h : Var) : (nb090_alpha_dummy_245 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0284 (A : Class) : (nb090_alpha_dummy_243 A) ∈ (((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0285 (h : Var) : (nb090_alpha_dummy_245 h) ∈ (((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0286 (A : Class) : (nb090_alpha_dummy_248 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0287 (h : Var) : (nb090_alpha_dummy_250 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0288 (A : Class) : (nb090_alpha_dummy_248 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0289 (h : Var) : (nb090_alpha_dummy_250 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0290 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0291 (h : Var) : h ∈ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0292 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0293 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (({(nb090_alpha_dummy_283 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_283 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0294 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_283 A) (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_283 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0293 A) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0292 A) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0295 (u : Var) : u ∈ (((syn_c2nd)).fv ∪ ((Class.cv u)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0296 (u : Var) : u ∈ (({(nb090_alpha_dummy_284 u)} : Finset Var) ∪ ((syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0297 (u : Var) : u ∈ (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_284 u) (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))) (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0296 u) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0295 u) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0298 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0299 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0300 (u : Var) : u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0301 (u : Var) : u ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0302 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0303 (u : Var) : u ∈ (((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0304 (A : Class) : (nb090_alpha_dummy_292 A) ∈ (((Class.cv (nb090_alpha_dummy_292 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0305 (u : Var) : (nb090_alpha_dummy_294 u) ∈ (((Class.cv (nb090_alpha_dummy_294 u))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0306 (A : Class) : (nb090_alpha_dummy_299 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_299 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_299 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_299 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0307 (u : Var) : (nb090_alpha_dummy_301 u) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_301 u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_301 u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_301 u))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0308 (A : Class) : (nb090_alpha_dummy_299 A) ∈ (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0309 (u : Var) : (nb090_alpha_dummy_301 u) ∈ (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0310 (A : Class) : (nb090_alpha_dummy_306 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0311 (u : Var) : (nb090_alpha_dummy_309 u) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0312 (A : Class) : (nb090_alpha_dummy_306 A) ∈ (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0313 (u : Var) : (nb090_alpha_dummy_309 u) ∈ (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0314 (A : Class) : (nb090_alpha_dummy_307 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0315 (u : Var) : (nb090_alpha_dummy_310 u) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0316 (A : Class) : (nb090_alpha_dummy_307 A) ∈ (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0317 (u : Var) : (nb090_alpha_dummy_310 u) ∈ (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0318 (A : Class) : (nb090_alpha_dummy_306 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_306 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_307 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0319 (u : Var) : (nb090_alpha_dummy_309 u) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_309 u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_310 u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0320 (A : Class) : (nb090_alpha_dummy_306 A) ∈ (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_306 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0321 (u : Var) : (nb090_alpha_dummy_309 u) ∈ (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_309 u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0322 (A : Class) : (nb090_alpha_dummy_307 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_306 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_307 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0323 (u : Var) : (nb090_alpha_dummy_310 u) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_309 u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_310 u)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0324 (A : Class) : (nb090_alpha_dummy_307 A) ∈ (((Class.cv (nb090_alpha_dummy_307 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0325 (u : Var) : (nb090_alpha_dummy_310 u) ∈ (((Class.cv (nb090_alpha_dummy_310 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0326 (A : Class) : (nb090_alpha_dummy_283 A) ∈ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0327 (A : Class) : (nb090_alpha_dummy_283 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0328 (u : Var) : (nb090_alpha_dummy_284 u) ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0329 (u : Var) : (nb090_alpha_dummy_284 u) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0330 (A : Class) : (nb090_alpha_dummy_283 A) ∈ (((Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0331 (u : Var) : (nb090_alpha_dummy_284 u) ∈ (((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0332 (A : Class) : (nb090_alpha_dummy_292 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0333 (u : Var) : (nb090_alpha_dummy_294 u) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0334 (A : Class) : (nb090_alpha_dummy_292 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0335 (u : Var) : (nb090_alpha_dummy_294 u) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0336 (A : Class) : (nb090_alpha_dummy_285 A) ∈ (((Class.cv (nb090_alpha_dummy_285 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0337 (u : Var) : (nb090_alpha_dummy_286 u) ∈ (((Class.cv (nb090_alpha_dummy_286 u))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0338 (A : Class) : (nb090_alpha_dummy_334 A) ∈ (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0339 (A : Class) : (nb090_alpha_dummy_334 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0340 (h : Var) : (nb090_alpha_dummy_336 h) ∈ (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0341 (h : Var) : (nb090_alpha_dummy_336 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0342 (A : Class) : (nb090_alpha_dummy_334 A) ∈ (((Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0343 (h : Var) : (nb090_alpha_dummy_336 h) ∈ (((Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0344 (A : Class) : (nb090_alpha_dummy_338 A) ∈ (((Class.cv (nb090_alpha_dummy_338 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0345 (h : Var) : (nb090_alpha_dummy_340 h) ∈ (((Class.cv (nb090_alpha_dummy_340 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0346 (A : Class) : (nb090_alpha_dummy_345 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_345 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_345 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_345 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0347 (h : Var) : (nb090_alpha_dummy_347 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_347 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_347 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_347 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0348 (A : Class) : (nb090_alpha_dummy_345 A) ∈ (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0349 (h : Var) : (nb090_alpha_dummy_347 h) ∈ (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0350 (A : Class) : (nb090_alpha_dummy_352 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0351 (h : Var) : (nb090_alpha_dummy_355 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0352 (A : Class) : (nb090_alpha_dummy_352 A) ∈ (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0353 (h : Var) : (nb090_alpha_dummy_355 h) ∈ (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0354 (A : Class) : (nb090_alpha_dummy_353 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0355 (h : Var) : (nb090_alpha_dummy_356 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
