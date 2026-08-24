import NAR4C057C001Part006

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

theorem nb057_support_mem_0246 : (nb057_alpha_dummy_045) ∈ (((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0247 (f : Var) : (nb057_alpha_dummy_048 f) ∈ (((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0248 : (nb057_alpha_dummy_203) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_203))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0249 (f : Var) : (nb057_alpha_dummy_205 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0250 : (nb057_alpha_dummy_203) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0251 (f : Var) : (nb057_alpha_dummy_205 f) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0252 : (nb057_alpha_dummy_239) ∈ (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0253 : (nb057_alpha_dummy_239) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0254 (f : Var) : (nb057_alpha_dummy_241 f) ∈ (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0255 (f : Var) : (nb057_alpha_dummy_241 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0256 : (nb057_alpha_dummy_239) ∈ (((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0257 (f : Var) : (nb057_alpha_dummy_241 f) ∈ (((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0258 : (nb057_alpha_dummy_243) ∈ (((Class.cv (nb057_alpha_dummy_243))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0259 (f : Var) : (nb057_alpha_dummy_245 f) ∈ (((Class.cv (nb057_alpha_dummy_245 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0260 : (nb057_alpha_dummy_250) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_250)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_250)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_250))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0261 (f : Var) : (nb057_alpha_dummy_252 f) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_252 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_252 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_252 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0262 : (nb057_alpha_dummy_250) ∈ (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0263 (f : Var) : (nb057_alpha_dummy_252 f) ∈ (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0264 : (nb057_alpha_dummy_257) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0265 (f : Var) : (nb057_alpha_dummy_260 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0266 : (nb057_alpha_dummy_257) ∈ (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0267 (f : Var) : (nb057_alpha_dummy_260 f) ∈ (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0268 : (nb057_alpha_dummy_258) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0269 (f : Var) : (nb057_alpha_dummy_261 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0270 : (nb057_alpha_dummy_258) ∈ (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0271 (f : Var) : (nb057_alpha_dummy_261 f) ∈ (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0272 : (nb057_alpha_dummy_257) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_257)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_258)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0273 (f : Var) : (nb057_alpha_dummy_260 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_260 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_261 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0274 : (nb057_alpha_dummy_257) ∈ (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_257))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0275 (f : Var) : (nb057_alpha_dummy_260 f) ∈ (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_260 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0276 : (nb057_alpha_dummy_258) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_257)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_258)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0277 (f : Var) : (nb057_alpha_dummy_261 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_260 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_261 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0278 : (nb057_alpha_dummy_258) ∈ (((Class.cv (nb057_alpha_dummy_258))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0279 (f : Var) : (nb057_alpha_dummy_261 f) ∈ (((Class.cv (nb057_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0280 : (nb057_alpha_dummy_238) ∈ (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0281 : (nb057_alpha_dummy_238) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0282 (f : Var) : (nb057_alpha_dummy_240 f) ∈ (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0283 (f : Var) : (nb057_alpha_dummy_240 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0284 : (nb057_alpha_dummy_238) ∈ (((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0285 (f : Var) : (nb057_alpha_dummy_240 f) ∈ (((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0286 : (nb057_alpha_dummy_243) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_243))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0287 (f : Var) : (nb057_alpha_dummy_245 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0288 : (nb057_alpha_dummy_243) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0289 (f : Var) : (nb057_alpha_dummy_245 f) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0290 : (nb057_alpha_dummy_001) ∈ (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0291 (f : Var) : f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_compact_fv_empty_0000 : (nb057_alpha_dummy_020) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0000 : (nb057_alpha_dummy_020) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_020, fv_syn_c1c] using (nb057_compact_fv_empty_0000)

theorem nb057_compact_fv_empty_0001 (f : Var) (a : Var) : (nb057_alpha_dummy_023 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0001 (f : Var) (a : Var) : (nb057_alpha_dummy_023 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_023, fv_syn_c1c] using (nb057_compact_fv_empty_0001 f a)

theorem nb057_compact_fv_empty_0002 : (nb057_alpha_dummy_019) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0002 : (nb057_alpha_dummy_019) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_019, fv_syn_c1c] using (nb057_compact_fv_empty_0002)

theorem nb057_compact_fv_empty_0003 (f : Var) (a : Var) : (nb057_alpha_dummy_022 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0003 (f : Var) (a : Var) : (nb057_alpha_dummy_022 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_022, fv_syn_c1c] using (nb057_compact_fv_empty_0003 f a)

theorem nb057_compact_fv_empty_0004 : (nb057_alpha_dummy_018) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0004 : (nb057_alpha_dummy_018) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_018, fv_syn_c1c] using (nb057_compact_fv_empty_0004)

theorem nb057_compact_fv_empty_0005 (f : Var) (a : Var) : (nb057_alpha_dummy_021 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0005 (f : Var) (a : Var) : (nb057_alpha_dummy_021 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_021, fv_syn_c1c] using (nb057_compact_fv_empty_0005 f a)

theorem nb057_compact_fv_empty_0006 : (nb057_alpha_dummy_016) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0006 : (nb057_alpha_dummy_016) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_016, fv_syn_c1c] using (nb057_compact_fv_empty_0006)

theorem nb057_compact_fv_empty_0007 (f : Var) (a : Var) : (nb057_alpha_dummy_017 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0007 (f : Var) (a : Var) : (nb057_alpha_dummy_017 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_017, fv_syn_c1c] using (nb057_compact_fv_empty_0007 f a)

theorem nb057_compact_fv_empty_0008 : (nb057_alpha_dummy_012) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0008 : (nb057_alpha_dummy_012) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_012, fv_syn_c1c] using (nb057_compact_fv_empty_0008)

theorem nb057_compact_fv_empty_0009 (f : Var) (a : Var) : (nb057_alpha_dummy_014 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0009 (f : Var) (a : Var) : (nb057_alpha_dummy_014 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_014, fv_syn_c1c] using (nb057_compact_fv_empty_0009 f a)

theorem nb057_compact_fv_empty_0010 : (nb057_alpha_dummy_013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0010 : (nb057_alpha_dummy_013) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_013, fv_syn_c1c] using (nb057_compact_fv_empty_0010)

theorem nb057_compact_fv_empty_0011 (f : Var) (a : Var) : (nb057_alpha_dummy_015 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0011 (f : Var) (a : Var) : (nb057_alpha_dummy_015 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_015, fv_syn_c1c] using (nb057_compact_fv_empty_0011 f a)

theorem nb057_compact_fv_empty_0012 : (nb057_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0012 : (nb057_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_005, fv_syn_c1c] using (nb057_compact_fv_empty_0012)

theorem nb057_compact_fv_empty_0013 (f : Var) (a : Var) : (nb057_alpha_dummy_007 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0013 (f : Var) (a : Var) : (nb057_alpha_dummy_007 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_007, fv_syn_c1c] using (nb057_compact_fv_empty_0013 f a)

theorem nb057_compact_fv_empty_0014 : (nb057_alpha_dummy_004) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0014 : (nb057_alpha_dummy_004) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_004, fv_syn_c1c] using (nb057_compact_fv_empty_0014)

theorem nb057_compact_fv_empty_0015 (f : Var) (a : Var) : (nb057_alpha_dummy_006 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0015 (f : Var) (a : Var) : (nb057_alpha_dummy_006 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_006, fv_syn_c1c] using (nb057_compact_fv_empty_0015 f a)

theorem nb057_compact_fv_empty_0016 : (nb057_alpha_dummy_010) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0016 : (nb057_alpha_dummy_010) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_010, fv_syn_c1c] using (nb057_compact_fv_empty_0016)

theorem nb057_compact_fv_empty_0017 (f : Var) (a : Var) : (nb057_alpha_dummy_011 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0017 (f : Var) (a : Var) : (nb057_alpha_dummy_011 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_011, fv_syn_c1c] using (nb057_compact_fv_empty_0017 f a)

theorem nb057_compact_fv_empty_0018 : (nb057_alpha_dummy_008) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0018 : (nb057_alpha_dummy_008) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_008, fv_syn_c1c] using (nb057_compact_fv_empty_0018)

theorem nb057_compact_fv_empty_0019 (f : Var) (a : Var) : (nb057_alpha_dummy_009 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0019 (f : Var) (a : Var) : (nb057_alpha_dummy_009 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_009, fv_syn_c1c] using (nb057_compact_fv_empty_0019 f a)

theorem nb057_compact_fv_empty_0020 : (nb057_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0020 : (nb057_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_000, fv_syn_c1c] using (nb057_compact_fv_empty_0020)

theorem nb057_compact_fv_empty_0021 (a : Var) : a ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0021 (a : Var) : a ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb057_compact_fv_empty_0021 a)

theorem nb057_compact_fv_empty_0022 : (nb057_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0022 : (nb057_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_001, fv_syn_c1c] using (nb057_compact_fv_empty_0022)

theorem nb057_compact_fv_empty_0023 (f : Var) : f ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0023 (f : Var) : f ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb057_compact_fv_empty_0023 f)

theorem nb057_compact_fv_empty_0024 : (nb057_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0024 : (nb057_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_002, fv_syn_c1c] using (nb057_compact_fv_empty_0024)

theorem nb057_compact_fv_empty_0025 (f : Var) (a : Var) : (nb057_alpha_dummy_003 f a) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0025 (f : Var) (a : Var) : (nb057_alpha_dummy_003 f a) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_003, fv_syn_c1c] using (nb057_compact_fv_empty_0025 f a)

theorem nb057_compact_envfresh_0000 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_020) (nb057_alpha_dummy_023 f a) (nb057_wpp_notmem_0000) (nb057_wpp_notmem_0001 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_019) (nb057_alpha_dummy_022 f a) (nb057_wpp_notmem_0002) (nb057_wpp_notmem_0003 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_018) (nb057_alpha_dummy_021 f a) (nb057_wpp_notmem_0004) (nb057_wpp_notmem_0005 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_016) (nb057_alpha_dummy_017 f a) (nb057_wpp_notmem_0006) (nb057_wpp_notmem_0007 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_012) (nb057_alpha_dummy_014 f a) (nb057_wpp_notmem_0008) (nb057_wpp_notmem_0009 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_013) (nb057_alpha_dummy_015 f a) (nb057_wpp_notmem_0010) (nb057_wpp_notmem_0011 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_005) (nb057_alpha_dummy_007 f a) (nb057_wpp_notmem_0012) (nb057_wpp_notmem_0013 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_004) (nb057_alpha_dummy_006 f a) (nb057_wpp_notmem_0014) (nb057_wpp_notmem_0015 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_010) (nb057_alpha_dummy_011 f a) (nb057_wpp_notmem_0016) (nb057_wpp_notmem_0017 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_008) (nb057_alpha_dummy_009 f a) (nb057_wpp_notmem_0018) (nb057_wpp_notmem_0019 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb057_wpp_refl_0000 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0000 f a)

theorem nb057_wpp_notmem_0026 : (nb057_alpha_dummy_020) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_020, fv_syn_c0] using (nb057_compact_fv_empty_0000)

theorem nb057_wpp_notmem_0027 (f : Var) (a : Var) : (nb057_alpha_dummy_023 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_023, fv_syn_c0] using (nb057_compact_fv_empty_0001 f a)

theorem nb057_wpp_notmem_0028 : (nb057_alpha_dummy_019) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_019, fv_syn_c0] using (nb057_compact_fv_empty_0002)

theorem nb057_wpp_notmem_0029 (f : Var) (a : Var) : (nb057_alpha_dummy_022 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_022, fv_syn_c0] using (nb057_compact_fv_empty_0003 f a)

theorem nb057_wpp_notmem_0030 : (nb057_alpha_dummy_018) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_018, fv_syn_c0] using (nb057_compact_fv_empty_0004)

theorem nb057_wpp_notmem_0031 (f : Var) (a : Var) : (nb057_alpha_dummy_021 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_021, fv_syn_c0] using (nb057_compact_fv_empty_0005 f a)

theorem nb057_wpp_notmem_0032 : (nb057_alpha_dummy_016) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_016, fv_syn_c0] using (nb057_compact_fv_empty_0006)

theorem nb057_wpp_notmem_0033 (f : Var) (a : Var) : (nb057_alpha_dummy_017 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_017, fv_syn_c0] using (nb057_compact_fv_empty_0007 f a)

theorem nb057_wpp_notmem_0034 : (nb057_alpha_dummy_012) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_012, fv_syn_c0] using (nb057_compact_fv_empty_0008)

theorem nb057_wpp_notmem_0035 (f : Var) (a : Var) : (nb057_alpha_dummy_014 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_014, fv_syn_c0] using (nb057_compact_fv_empty_0009 f a)

theorem nb057_wpp_notmem_0036 : (nb057_alpha_dummy_013) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_013, fv_syn_c0] using (nb057_compact_fv_empty_0010)

theorem nb057_wpp_notmem_0037 (f : Var) (a : Var) : (nb057_alpha_dummy_015 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_015, fv_syn_c0] using (nb057_compact_fv_empty_0011 f a)

theorem nb057_wpp_notmem_0038 : (nb057_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_005, fv_syn_c0] using (nb057_compact_fv_empty_0012)

theorem nb057_wpp_notmem_0039 (f : Var) (a : Var) : (nb057_alpha_dummy_007 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_007, fv_syn_c0] using (nb057_compact_fv_empty_0013 f a)

theorem nb057_wpp_notmem_0040 : (nb057_alpha_dummy_004) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_004, fv_syn_c0] using (nb057_compact_fv_empty_0014)

theorem nb057_wpp_notmem_0041 (f : Var) (a : Var) : (nb057_alpha_dummy_006 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_006, fv_syn_c0] using (nb057_compact_fv_empty_0015 f a)

theorem nb057_wpp_notmem_0042 : (nb057_alpha_dummy_010) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_010, fv_syn_c0] using (nb057_compact_fv_empty_0016)

theorem nb057_wpp_notmem_0043 (f : Var) (a : Var) : (nb057_alpha_dummy_011 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_011, fv_syn_c0] using (nb057_compact_fv_empty_0017 f a)

theorem nb057_wpp_notmem_0044 : (nb057_alpha_dummy_008) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_008, fv_syn_c0] using (nb057_compact_fv_empty_0018)

theorem nb057_wpp_notmem_0045 (f : Var) (a : Var) : (nb057_alpha_dummy_009 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_009, fv_syn_c0] using (nb057_compact_fv_empty_0019 f a)

theorem nb057_wpp_notmem_0046 : (nb057_alpha_dummy_000) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_000, fv_syn_c0] using (nb057_compact_fv_empty_0020)

theorem nb057_wpp_notmem_0047 (a : Var) : a ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb057_compact_fv_empty_0021 a)

theorem nb057_wpp_notmem_0048 : (nb057_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_001, fv_syn_c0] using (nb057_compact_fv_empty_0022)

theorem nb057_wpp_notmem_0049 (f : Var) : f ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb057_compact_fv_empty_0023 f)

theorem nb057_wpp_notmem_0050 : (nb057_alpha_dummy_002) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_002, fv_syn_c0] using (nb057_compact_fv_empty_0024)

theorem nb057_wpp_notmem_0051 (f : Var) (a : Var) : (nb057_alpha_dummy_003 f a) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_003, fv_syn_c0] using (nb057_compact_fv_empty_0025 f a)

theorem nb057_compact_envfresh_0001 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_020) (nb057_alpha_dummy_023 f a) (nb057_wpp_notmem_0026) (nb057_wpp_notmem_0027 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_019) (nb057_alpha_dummy_022 f a) (nb057_wpp_notmem_0028) (nb057_wpp_notmem_0029 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_018) (nb057_alpha_dummy_021 f a) (nb057_wpp_notmem_0030) (nb057_wpp_notmem_0031 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_016) (nb057_alpha_dummy_017 f a) (nb057_wpp_notmem_0032) (nb057_wpp_notmem_0033 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_012) (nb057_alpha_dummy_014 f a) (nb057_wpp_notmem_0034) (nb057_wpp_notmem_0035 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_013) (nb057_alpha_dummy_015 f a) (nb057_wpp_notmem_0036) (nb057_wpp_notmem_0037 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_005) (nb057_alpha_dummy_007 f a) (nb057_wpp_notmem_0038) (nb057_wpp_notmem_0039 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_004) (nb057_alpha_dummy_006 f a) (nb057_wpp_notmem_0040) (nb057_wpp_notmem_0041 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_010) (nb057_alpha_dummy_011 f a) (nb057_wpp_notmem_0042) (nb057_wpp_notmem_0043 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_008) (nb057_alpha_dummy_009 f a) (nb057_wpp_notmem_0044) (nb057_wpp_notmem_0045 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb057_wpp_refl_0001 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0001 f a)

noncomputable def nb057_split_alpha_0000 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_018)) (syn_cun (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_021 f a)) (syn_cun (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0019 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0017 f a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0023 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0021 f a) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0019 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0017 f a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0023 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0021 f a) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)), ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c0) (nb057_wpp_refl_0001 f a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0027 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0025 f a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0027 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0025 f a) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0031 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0029 f a) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0031 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0029 f a) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb057_wpp_notmem_0052 : (nb057_alpha_dummy_016) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_016, fv_syn_cnnc] using (nb057_compact_fv_empty_0006)

theorem nb057_wpp_notmem_0053 (f : Var) (a : Var) : (nb057_alpha_dummy_017 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_017, fv_syn_cnnc] using (nb057_compact_fv_empty_0007 f a)

theorem nb057_wpp_notmem_0054 : (nb057_alpha_dummy_012) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_012, fv_syn_cnnc] using (nb057_compact_fv_empty_0008)

theorem nb057_wpp_notmem_0055 (f : Var) (a : Var) : (nb057_alpha_dummy_014 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_014, fv_syn_cnnc] using (nb057_compact_fv_empty_0009 f a)

theorem nb057_wpp_notmem_0056 : (nb057_alpha_dummy_013) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_013, fv_syn_cnnc] using (nb057_compact_fv_empty_0010)

theorem nb057_wpp_notmem_0057 (f : Var) (a : Var) : (nb057_alpha_dummy_015 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_015, fv_syn_cnnc] using (nb057_compact_fv_empty_0011 f a)

theorem nb057_wpp_notmem_0058 : (nb057_alpha_dummy_005) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_005, fv_syn_cnnc] using (nb057_compact_fv_empty_0012)

theorem nb057_wpp_notmem_0059 (f : Var) (a : Var) : (nb057_alpha_dummy_007 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_007, fv_syn_cnnc] using (nb057_compact_fv_empty_0013 f a)

theorem nb057_wpp_notmem_0060 : (nb057_alpha_dummy_004) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_004, fv_syn_cnnc] using (nb057_compact_fv_empty_0014)

theorem nb057_wpp_notmem_0061 (f : Var) (a : Var) : (nb057_alpha_dummy_006 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_006, fv_syn_cnnc] using (nb057_compact_fv_empty_0015 f a)

theorem nb057_wpp_notmem_0062 : (nb057_alpha_dummy_010) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_010, fv_syn_cnnc] using (nb057_compact_fv_empty_0016)

theorem nb057_wpp_notmem_0063 (f : Var) (a : Var) : (nb057_alpha_dummy_011 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_011, fv_syn_cnnc] using (nb057_compact_fv_empty_0017 f a)

theorem nb057_wpp_notmem_0064 : (nb057_alpha_dummy_008) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_008, fv_syn_cnnc] using (nb057_compact_fv_empty_0018)

theorem nb057_wpp_notmem_0065 (f : Var) (a : Var) : (nb057_alpha_dummy_009 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_009, fv_syn_cnnc] using (nb057_compact_fv_empty_0019 f a)

theorem nb057_wpp_notmem_0066 : (nb057_alpha_dummy_000) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_000, fv_syn_cnnc] using (nb057_compact_fv_empty_0020)

theorem nb057_wpp_notmem_0067 (a : Var) : a ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb057_compact_fv_empty_0021 a)

theorem nb057_wpp_notmem_0068 : (nb057_alpha_dummy_001) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_001, fv_syn_cnnc] using (nb057_compact_fv_empty_0022)

theorem nb057_wpp_notmem_0069 (f : Var) : f ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb057_compact_fv_empty_0023 f)

theorem nb057_wpp_notmem_0070 : (nb057_alpha_dummy_002) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_002, fv_syn_cnnc] using (nb057_compact_fv_empty_0024)

theorem nb057_wpp_notmem_0071 (f : Var) (a : Var) : (nb057_alpha_dummy_003 f a) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_003, fv_syn_cnnc] using (nb057_compact_fv_empty_0025 f a)

theorem nb057_compact_envfresh_0002 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)), ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_016) (nb057_alpha_dummy_017 f a) (nb057_wpp_notmem_0052) (nb057_wpp_notmem_0053 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_012) (nb057_alpha_dummy_014 f a) (nb057_wpp_notmem_0054) (nb057_wpp_notmem_0055 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_013) (nb057_alpha_dummy_015 f a) (nb057_wpp_notmem_0056) (nb057_wpp_notmem_0057 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_005) (nb057_alpha_dummy_007 f a) (nb057_wpp_notmem_0058) (nb057_wpp_notmem_0059 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_004) (nb057_alpha_dummy_006 f a) (nb057_wpp_notmem_0060) (nb057_wpp_notmem_0061 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_010) (nb057_alpha_dummy_011 f a) (nb057_wpp_notmem_0062) (nb057_wpp_notmem_0063 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_008) (nb057_alpha_dummy_009 f a) (nb057_wpp_notmem_0064) (nb057_wpp_notmem_0065 f a) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0066) (nb057_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0068) (nb057_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0070) (nb057_wpp_notmem_0071 f a) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
