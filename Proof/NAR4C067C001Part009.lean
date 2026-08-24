import NAR4C067C001Part008

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

theorem nb067_support_mem_0320 : (nb067_alpha_dummy_297) ∈ (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0321 (f : Var) : (nb067_alpha_dummy_300 f) ∈ (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0322 : (nb067_alpha_dummy_296) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_296)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_297)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0323 (f : Var) : (nb067_alpha_dummy_299 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_299 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_300 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0324 : (nb067_alpha_dummy_296) ∈ (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_296))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0325 (f : Var) : (nb067_alpha_dummy_299 f) ∈ (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_299 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0326 : (nb067_alpha_dummy_297) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_296)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_297)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0327 (f : Var) : (nb067_alpha_dummy_300 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_299 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_300 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0328 : (nb067_alpha_dummy_297) ∈ (((Class.cv (nb067_alpha_dummy_297))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0329 (f : Var) : (nb067_alpha_dummy_300 f) ∈ (((Class.cv (nb067_alpha_dummy_300 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0330 : (nb067_alpha_dummy_277) ∈ (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0331 : (nb067_alpha_dummy_277) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0332 (f : Var) : (nb067_alpha_dummy_279 f) ∈ (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0333 (f : Var) : (nb067_alpha_dummy_279 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0334 : (nb067_alpha_dummy_277) ∈ (((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0330) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0335 (f : Var) : (nb067_alpha_dummy_279 f) ∈ (((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0332 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0336 : (nb067_alpha_dummy_282) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_282))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0337 (f : Var) : (nb067_alpha_dummy_284 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0338 : (nb067_alpha_dummy_282) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0339 (f : Var) : (nb067_alpha_dummy_284 f) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0340 : (nb067_alpha_dummy_000) ∈ (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0341 (f : Var) : f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0342 : (nb067_alpha_dummy_322) ∈ (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0343 : (nb067_alpha_dummy_322) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0344 (f : Var) : (nb067_alpha_dummy_324 f) ∈ (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0345 (f : Var) : (nb067_alpha_dummy_324 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0346 : (nb067_alpha_dummy_322) ∈ (((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0342) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0347 (f : Var) : (nb067_alpha_dummy_324 f) ∈ (((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0344 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0348 : (nb067_alpha_dummy_326) ∈ (((Class.cv (nb067_alpha_dummy_326))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0349 (f : Var) : (nb067_alpha_dummy_328 f) ∈ (((Class.cv (nb067_alpha_dummy_328 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0350 : (nb067_alpha_dummy_333) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_333))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0351 (f : Var) : (nb067_alpha_dummy_335 f) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_335 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0352 : (nb067_alpha_dummy_333) ∈ (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0353 (f : Var) : (nb067_alpha_dummy_335 f) ∈ (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0354 : (nb067_alpha_dummy_340) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0355 (f : Var) : (nb067_alpha_dummy_343 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0356 : (nb067_alpha_dummy_340) ∈ (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0357 (f : Var) : (nb067_alpha_dummy_343 f) ∈ (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0358 : (nb067_alpha_dummy_341) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0359 (f : Var) : (nb067_alpha_dummy_344 f) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0360 : (nb067_alpha_dummy_341) ∈ (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0361 (f : Var) : (nb067_alpha_dummy_344 f) ∈ (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0362 : (nb067_alpha_dummy_340) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_340)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_341)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0363 (f : Var) : (nb067_alpha_dummy_343 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_343 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_344 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0364 : (nb067_alpha_dummy_340) ∈ (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_340))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0365 (f : Var) : (nb067_alpha_dummy_343 f) ∈ (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_343 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0366 : (nb067_alpha_dummy_341) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_340)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_341)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0367 (f : Var) : (nb067_alpha_dummy_344 f) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_343 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_344 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0368 : (nb067_alpha_dummy_341) ∈ (((Class.cv (nb067_alpha_dummy_341))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0369 (f : Var) : (nb067_alpha_dummy_344 f) ∈ (((Class.cv (nb067_alpha_dummy_344 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0370 : (nb067_alpha_dummy_321) ∈ (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0371 : (nb067_alpha_dummy_321) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0372 (f : Var) : (nb067_alpha_dummy_323 f) ∈ (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0373 (f : Var) : (nb067_alpha_dummy_323 f) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0374 : (nb067_alpha_dummy_321) ∈ (((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0370) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0375 (f : Var) : (nb067_alpha_dummy_323 f) ∈ (((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0372 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0376 : (nb067_alpha_dummy_326) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_326))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0377 (f : Var) : (nb067_alpha_dummy_328 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0378 : (nb067_alpha_dummy_326) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0379 (f : Var) : (nb067_alpha_dummy_328 f) ∈ (((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0380 : (nb067_alpha_dummy_000) ∈ (((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_001)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_001)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0381 (x : Var) (f : Var) : f ∈ (((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv ∪ ((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0382 : (nb067_alpha_dummy_000) ∈ (((syn_crn (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((Class.cv (nb067_alpha_dummy_001))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0383 (x : Var) (f : Var) : f ∈ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv x)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0384 : (nb067_alpha_dummy_000) ∈ (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0385 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0386 : (nb067_alpha_dummy_001) ∈ (((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_001)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_001)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0387 (x : Var) (f : Var) : x ∈ (((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv ∪ ((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0388 : (nb067_alpha_dummy_001) ∈ (((syn_crn (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((Class.cv (nb067_alpha_dummy_001))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0389 (x : Var) (f : Var) : x ∈ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv x)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_compact_fv_empty_0000 : (nb067_alpha_dummy_031) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0000 : (nb067_alpha_dummy_031) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_031, fv_syn_c1c] using (nb067_compact_fv_empty_0000)

theorem nb067_compact_fv_empty_0001 (x : Var) (y : Var) : (nb067_alpha_dummy_034 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0001 (x : Var) (y : Var) : (nb067_alpha_dummy_034 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_034, fv_syn_c1c] using (nb067_compact_fv_empty_0001 x y)

theorem nb067_compact_fv_empty_0002 : (nb067_alpha_dummy_030) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0002 : (nb067_alpha_dummy_030) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_030, fv_syn_c1c] using (nb067_compact_fv_empty_0002)

theorem nb067_compact_fv_empty_0003 (x : Var) (y : Var) : (nb067_alpha_dummy_033 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0003 (x : Var) (y : Var) : (nb067_alpha_dummy_033 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_033, fv_syn_c1c] using (nb067_compact_fv_empty_0003 x y)

theorem nb067_compact_fv_empty_0004 : (nb067_alpha_dummy_029) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0004 : (nb067_alpha_dummy_029) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_029, fv_syn_c1c] using (nb067_compact_fv_empty_0004)

theorem nb067_compact_fv_empty_0005 (x : Var) (y : Var) : (nb067_alpha_dummy_032 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0005 (x : Var) (y : Var) : (nb067_alpha_dummy_032 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_032, fv_syn_c1c] using (nb067_compact_fv_empty_0005 x y)

theorem nb067_compact_fv_empty_0006 : (nb067_alpha_dummy_027) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0006 : (nb067_alpha_dummy_027) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_027, fv_syn_c1c] using (nb067_compact_fv_empty_0006)

theorem nb067_compact_fv_empty_0007 (x : Var) (y : Var) : (nb067_alpha_dummy_028 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0007 (x : Var) (y : Var) : (nb067_alpha_dummy_028 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_028, fv_syn_c1c] using (nb067_compact_fv_empty_0007 x y)

theorem nb067_compact_fv_empty_0008 : (nb067_alpha_dummy_023) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0008 : (nb067_alpha_dummy_023) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_023, fv_syn_c1c] using (nb067_compact_fv_empty_0008)

theorem nb067_compact_fv_empty_0009 (x : Var) (y : Var) : (nb067_alpha_dummy_025 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0009 (x : Var) (y : Var) : (nb067_alpha_dummy_025 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_025, fv_syn_c1c] using (nb067_compact_fv_empty_0009 x y)

theorem nb067_compact_fv_empty_0010 : (nb067_alpha_dummy_024) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0010 : (nb067_alpha_dummy_024) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_024, fv_syn_c1c] using (nb067_compact_fv_empty_0010)

theorem nb067_compact_fv_empty_0011 (x : Var) (y : Var) : (nb067_alpha_dummy_026 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0011 (x : Var) (y : Var) : (nb067_alpha_dummy_026 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_026, fv_syn_c1c] using (nb067_compact_fv_empty_0011 x y)

theorem nb067_compact_fv_empty_0012 : (nb067_alpha_dummy_016) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0012 : (nb067_alpha_dummy_016) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_016, fv_syn_c1c] using (nb067_compact_fv_empty_0012)

theorem nb067_compact_fv_empty_0013 (x : Var) (y : Var) : (nb067_alpha_dummy_018 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0013 (x : Var) (y : Var) : (nb067_alpha_dummy_018 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_018, fv_syn_c1c] using (nb067_compact_fv_empty_0013 x y)

theorem nb067_compact_fv_empty_0014 : (nb067_alpha_dummy_015) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0014 : (nb067_alpha_dummy_015) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_015, fv_syn_c1c] using (nb067_compact_fv_empty_0014)

theorem nb067_compact_fv_empty_0015 (x : Var) (y : Var) : (nb067_alpha_dummy_017 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0015 (x : Var) (y : Var) : (nb067_alpha_dummy_017 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_017, fv_syn_c1c] using (nb067_compact_fv_empty_0015 x y)

theorem nb067_compact_fv_empty_0016 : (nb067_alpha_dummy_021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0016 : (nb067_alpha_dummy_021) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_021, fv_syn_c1c] using (nb067_compact_fv_empty_0016)

theorem nb067_compact_fv_empty_0017 (x : Var) (y : Var) : (nb067_alpha_dummy_022 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0017 (x : Var) (y : Var) : (nb067_alpha_dummy_022 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_022, fv_syn_c1c] using (nb067_compact_fv_empty_0017 x y)

theorem nb067_compact_fv_empty_0018 : (nb067_alpha_dummy_019) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0018 : (nb067_alpha_dummy_019) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_019, fv_syn_c1c] using (nb067_compact_fv_empty_0018)

theorem nb067_compact_fv_empty_0019 (x : Var) (y : Var) : (nb067_alpha_dummy_020 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0019 (x : Var) (y : Var) : (nb067_alpha_dummy_020 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_020, fv_syn_c1c] using (nb067_compact_fv_empty_0019 x y)

theorem nb067_compact_fv_empty_0020 : (nb067_alpha_dummy_008) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0020 : (nb067_alpha_dummy_008) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_008, fv_syn_c1c] using (nb067_compact_fv_empty_0020)

theorem nb067_compact_fv_empty_0021 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_010 x y f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0021 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_010 x y f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_010, fv_syn_c1c] using (nb067_compact_fv_empty_0021 x y f)

theorem nb067_compact_fv_empty_0022 : (nb067_alpha_dummy_007) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0022 : (nb067_alpha_dummy_007) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_007, fv_syn_c1c] using (nb067_compact_fv_empty_0022)

theorem nb067_compact_fv_empty_0023 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_009 x y f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0023 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_009 x y f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_009, fv_syn_c1c] using (nb067_compact_fv_empty_0023 x y f)

theorem nb067_compact_fv_empty_0024 : (nb067_alpha_dummy_013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0024 : (nb067_alpha_dummy_013) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_013, fv_syn_c1c] using (nb067_compact_fv_empty_0024)

theorem nb067_compact_fv_empty_0025 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_014 x y f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0025 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_014 x y f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_014, fv_syn_c1c] using (nb067_compact_fv_empty_0025 x y f)

theorem nb067_compact_fv_empty_0026 : (nb067_alpha_dummy_011) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0026 : (nb067_alpha_dummy_011) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_011, fv_syn_c1c] using (nb067_compact_fv_empty_0026)

theorem nb067_compact_fv_empty_0027 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_012 x y f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0027 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_012 x y f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_012, fv_syn_c1c] using (nb067_compact_fv_empty_0027 x y f)

theorem nb067_compact_fv_empty_0028 : (nb067_alpha_dummy_003) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0028 : (nb067_alpha_dummy_003) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_003, fv_syn_c1c] using (nb067_compact_fv_empty_0028)

theorem nb067_compact_fv_empty_0029 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_004 x y f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0029 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_004 x y f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_004, fv_syn_c1c] using (nb067_compact_fv_empty_0029 x y f)

theorem nb067_compact_fv_empty_0030 : (nb067_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0030 : (nb067_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_002, fv_syn_c1c] using (nb067_compact_fv_empty_0030)

theorem nb067_compact_fv_empty_0031 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0031 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb067_compact_fv_empty_0031 y)

theorem nb067_compact_fv_empty_0032 : (nb067_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0032 : (nb067_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_001, fv_syn_c1c] using (nb067_compact_fv_empty_0032)

theorem nb067_compact_fv_empty_0033 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0033 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb067_compact_fv_empty_0033 x)

theorem nb067_compact_fv_empty_0034 : (nb067_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0034 : (nb067_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_005, fv_syn_c1c] using (nb067_compact_fv_empty_0034)

theorem nb067_compact_fv_empty_0035 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_006 x y f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0035 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_006 x y f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_006, fv_syn_c1c] using (nb067_compact_fv_empty_0035 x y f)

theorem nb067_compact_envfresh_0000 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_031) (nb067_alpha_dummy_034 x y) (nb067_wpp_notmem_0000) (nb067_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_030) (nb067_alpha_dummy_033 x y) (nb067_wpp_notmem_0002) (nb067_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_029) (nb067_alpha_dummy_032 x y) (nb067_wpp_notmem_0004) (nb067_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_027) (nb067_alpha_dummy_028 x y) (nb067_wpp_notmem_0006) (nb067_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_023) (nb067_alpha_dummy_025 x y) (nb067_wpp_notmem_0008) (nb067_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_024) (nb067_alpha_dummy_026 x y) (nb067_wpp_notmem_0010) (nb067_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_016) (nb067_alpha_dummy_018 x y) (nb067_wpp_notmem_0012) (nb067_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_015) (nb067_alpha_dummy_017 x y) (nb067_wpp_notmem_0014) (nb067_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_021) (nb067_alpha_dummy_022 x y) (nb067_wpp_notmem_0016) (nb067_wpp_notmem_0017 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_019) (nb067_alpha_dummy_020 x y) (nb067_wpp_notmem_0018) (nb067_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb067_alpha_dummy_008) (nb067_alpha_dummy_010 x y f) (nb067_wpp_notmem_0020) (nb067_wpp_notmem_0021 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_007) (nb067_alpha_dummy_009 x y f) (nb067_wpp_notmem_0022) (nb067_wpp_notmem_0023 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_013) (nb067_alpha_dummy_014 x y f) (nb067_wpp_notmem_0024) (nb067_wpp_notmem_0025 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_011) (nb067_alpha_dummy_012 x y f) (nb067_wpp_notmem_0026) (nb067_wpp_notmem_0027 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb067_wpp_refl_0000 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0000 x y f)

theorem nb067_wpp_notmem_0036 : (nb067_alpha_dummy_031) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_031, fv_syn_c0] using (nb067_compact_fv_empty_0000)

theorem nb067_wpp_notmem_0037 (x : Var) (y : Var) : (nb067_alpha_dummy_034 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_034, fv_syn_c0] using (nb067_compact_fv_empty_0001 x y)

theorem nb067_wpp_notmem_0038 : (nb067_alpha_dummy_030) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_030, fv_syn_c0] using (nb067_compact_fv_empty_0002)

theorem nb067_wpp_notmem_0039 (x : Var) (y : Var) : (nb067_alpha_dummy_033 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_033, fv_syn_c0] using (nb067_compact_fv_empty_0003 x y)

theorem nb067_wpp_notmem_0040 : (nb067_alpha_dummy_029) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_029, fv_syn_c0] using (nb067_compact_fv_empty_0004)

theorem nb067_wpp_notmem_0041 (x : Var) (y : Var) : (nb067_alpha_dummy_032 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_032, fv_syn_c0] using (nb067_compact_fv_empty_0005 x y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
