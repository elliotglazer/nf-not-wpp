import NAR4C078C001Part023

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

theorem nb078_support_mem_0313 (g : Var) : (nb078_alpha_dummy_314 g) ∈ (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0314 : (nb078_alpha_dummy_310) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_310)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_311)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0315 (g : Var) : (nb078_alpha_dummy_313 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_313 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_314 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0316 : (nb078_alpha_dummy_310) ∈ (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_310))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0317 (g : Var) : (nb078_alpha_dummy_313 g) ∈ (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_313 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0318 : (nb078_alpha_dummy_311) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_310)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_311)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0319 (g : Var) : (nb078_alpha_dummy_314 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_313 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_314 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0320 : (nb078_alpha_dummy_311) ∈ (((Class.cv (nb078_alpha_dummy_311))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0321 (g : Var) : (nb078_alpha_dummy_314 g) ∈ (((Class.cv (nb078_alpha_dummy_314 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0322 : (nb078_alpha_dummy_288) ∈ (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0323 : (nb078_alpha_dummy_288) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cphi (Class.cv (nb078_alpha_dummy_296)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0324 (g : Var) : (nb078_alpha_dummy_291 g) ∈ (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0325 (g : Var) : (nb078_alpha_dummy_291 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0326 : (nb078_alpha_dummy_288) ∈ (((Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0322) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0327 (g : Var) : (nb078_alpha_dummy_291 g) ∈ (((Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0324 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0328 : (nb078_alpha_dummy_296) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_296))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0329 (g : Var) : (nb078_alpha_dummy_298 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0330 : (nb078_alpha_dummy_296) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0331 (g : Var) : (nb078_alpha_dummy_298 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0332 : (nb078_alpha_dummy_287) ∈ (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0333 : (nb078_alpha_dummy_287) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cphi (Class.cv (nb078_alpha_dummy_332)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0334 (g : Var) : (nb078_alpha_dummy_290 g) ∈ (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0335 (g : Var) : (nb078_alpha_dummy_290 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0336 : (nb078_alpha_dummy_287) ∈ (((Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0332) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0337 (g : Var) : (nb078_alpha_dummy_290 g) ∈ (((Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0334 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0338 : (nb078_alpha_dummy_332) ∈ (((Class.cv (nb078_alpha_dummy_332))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0339 (g : Var) : (nb078_alpha_dummy_334 g) ∈ (((Class.cv (nb078_alpha_dummy_334 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0340 : (nb078_alpha_dummy_339) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_339)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_339)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_339))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0341 (g : Var) : (nb078_alpha_dummy_341 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_341 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_341 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_341 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0342 : (nb078_alpha_dummy_339) ∈ (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0343 (g : Var) : (nb078_alpha_dummy_341 g) ∈ (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0344 : (nb078_alpha_dummy_346) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0345 (g : Var) : (nb078_alpha_dummy_349 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0346 : (nb078_alpha_dummy_346) ∈ (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0347 (g : Var) : (nb078_alpha_dummy_349 g) ∈ (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0348 : (nb078_alpha_dummy_347) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0349 (g : Var) : (nb078_alpha_dummy_350 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0350 : (nb078_alpha_dummy_347) ∈ (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0351 (g : Var) : (nb078_alpha_dummy_350 g) ∈ (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0352 : (nb078_alpha_dummy_346) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_346)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_347)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0353 (g : Var) : (nb078_alpha_dummy_349 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_349 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_350 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0354 : (nb078_alpha_dummy_346) ∈ (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_346))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0355 (g : Var) : (nb078_alpha_dummy_349 g) ∈ (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_349 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0356 : (nb078_alpha_dummy_347) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_346)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_347)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0357 (g : Var) : (nb078_alpha_dummy_350 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_349 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_350 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0358 : (nb078_alpha_dummy_347) ∈ (((Class.cv (nb078_alpha_dummy_347))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0359 (g : Var) : (nb078_alpha_dummy_350 g) ∈ (((Class.cv (nb078_alpha_dummy_350 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0360 : (nb078_alpha_dummy_289) ∈ (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0361 : (nb078_alpha_dummy_289) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cphi (Class.cv (nb078_alpha_dummy_332)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0362 (g : Var) : (nb078_alpha_dummy_292 g) ∈ (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0363 (g : Var) : (nb078_alpha_dummy_292 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0364 : (nb078_alpha_dummy_289) ∈ (((Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0360) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0365 (g : Var) : (nb078_alpha_dummy_292 g) ∈ (((Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0362 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0366 : (nb078_alpha_dummy_332) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_332))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0367 (g : Var) : (nb078_alpha_dummy_334 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0368 : (nb078_alpha_dummy_332) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0369 (g : Var) : (nb078_alpha_dummy_334 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0370 : (nb078_alpha_dummy_367) ∈ (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_367)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0371 (g : Var) : (nb078_alpha_dummy_369 g) ∈ (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_369 g)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0372 : (nb078_alpha_dummy_368) ∈ (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_367)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0373 (g : Var) : (nb078_alpha_dummy_370 g) ∈ (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_369 g)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0374 : (nb078_alpha_dummy_367) ∈ (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0375 : (nb078_alpha_dummy_367) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0376 (g : Var) : (nb078_alpha_dummy_369 g) ∈ (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0377 (g : Var) : (nb078_alpha_dummy_369 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0378 : (nb078_alpha_dummy_367) ∈ (((Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0379 (g : Var) : (nb078_alpha_dummy_369 g) ∈ (((Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0380 : (nb078_alpha_dummy_374) ∈ (((Class.cv (nb078_alpha_dummy_374))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0381 (g : Var) : (nb078_alpha_dummy_376 g) ∈ (((Class.cv (nb078_alpha_dummy_376 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0382 : (nb078_alpha_dummy_381) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_381)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_381)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_381))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0383 (g : Var) : (nb078_alpha_dummy_383 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_383 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_383 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_383 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0384 : (nb078_alpha_dummy_381) ∈ (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0385 (g : Var) : (nb078_alpha_dummy_383 g) ∈ (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0386 : (nb078_alpha_dummy_388) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0387 (g : Var) : (nb078_alpha_dummy_391 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0388 : (nb078_alpha_dummy_388) ∈ (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0389 (g : Var) : (nb078_alpha_dummy_391 g) ∈ (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0390 : (nb078_alpha_dummy_389) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0391 (g : Var) : (nb078_alpha_dummy_392 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0392 : (nb078_alpha_dummy_389) ∈ (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0393 (g : Var) : (nb078_alpha_dummy_392 g) ∈ (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0394 : (nb078_alpha_dummy_388) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_388)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_389)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0395 (g : Var) : (nb078_alpha_dummy_391 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_391 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_392 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0396 : (nb078_alpha_dummy_388) ∈ (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_388))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0397 (g : Var) : (nb078_alpha_dummy_391 g) ∈ (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_391 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0398 : (nb078_alpha_dummy_389) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_388)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_389)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0399 (g : Var) : (nb078_alpha_dummy_392 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_391 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_392 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0400 : (nb078_alpha_dummy_389) ∈ (((Class.cv (nb078_alpha_dummy_389))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0401 (g : Var) : (nb078_alpha_dummy_392 g) ∈ (((Class.cv (nb078_alpha_dummy_392 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0402 : (nb078_alpha_dummy_368) ∈ (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0403 : (nb078_alpha_dummy_368) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0404 (g : Var) : (nb078_alpha_dummy_370 g) ∈ (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0405 (g : Var) : (nb078_alpha_dummy_370 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0406 : (nb078_alpha_dummy_368) ∈ (((Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0402) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0407 (g : Var) : (nb078_alpha_dummy_370 g) ∈ (((Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0404 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0408 : (nb078_alpha_dummy_374) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_374))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0409 (g : Var) : (nb078_alpha_dummy_376 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0410 : (nb078_alpha_dummy_374) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0411 (g : Var) : (nb078_alpha_dummy_376 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0412 : (nb078_alpha_dummy_368) ∈ (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0413 : (nb078_alpha_dummy_368) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cphi (Class.cv (nb078_alpha_dummy_410)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0414 (g : Var) : (nb078_alpha_dummy_370 g) ∈ (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0415 (g : Var) : (nb078_alpha_dummy_370 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0416 : (nb078_alpha_dummy_368) ∈ (((Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0417 (g : Var) : (nb078_alpha_dummy_370 g) ∈ (((Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0418 : (nb078_alpha_dummy_410) ∈ (((Class.cv (nb078_alpha_dummy_410))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0419 (g : Var) : (nb078_alpha_dummy_412 g) ∈ (((Class.cv (nb078_alpha_dummy_412 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0420 : (nb078_alpha_dummy_417) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_417)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_417)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_417))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0421 (g : Var) : (nb078_alpha_dummy_419 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_419 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_419 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_419 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0422 : (nb078_alpha_dummy_417) ∈ (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0423 (g : Var) : (nb078_alpha_dummy_419 g) ∈ (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0424 : (nb078_alpha_dummy_424) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0425 (g : Var) : (nb078_alpha_dummy_427 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0426 : (nb078_alpha_dummy_424) ∈ (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0427 (g : Var) : (nb078_alpha_dummy_427 g) ∈ (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0428 : (nb078_alpha_dummy_425) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0429 (g : Var) : (nb078_alpha_dummy_428 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0430 : (nb078_alpha_dummy_425) ∈ (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0431 (g : Var) : (nb078_alpha_dummy_428 g) ∈ (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0432 : (nb078_alpha_dummy_424) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_424)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_425)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0433 (g : Var) : (nb078_alpha_dummy_427 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_427 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_428 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0434 : (nb078_alpha_dummy_424) ∈ (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_424))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0435 (g : Var) : (nb078_alpha_dummy_427 g) ∈ (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_427 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0436 : (nb078_alpha_dummy_425) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_424)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_425)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0437 (g : Var) : (nb078_alpha_dummy_428 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_427 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_428 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0438 : (nb078_alpha_dummy_425) ∈ (((Class.cv (nb078_alpha_dummy_425))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0439 (g : Var) : (nb078_alpha_dummy_428 g) ∈ (((Class.cv (nb078_alpha_dummy_428 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0440 : (nb078_alpha_dummy_367) ∈ (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0441 : (nb078_alpha_dummy_367) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cphi (Class.cv (nb078_alpha_dummy_410)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0442 (g : Var) : (nb078_alpha_dummy_369 g) ∈ (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0443 (g : Var) : (nb078_alpha_dummy_369 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0444 : (nb078_alpha_dummy_367) ∈ (((Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0440) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0445 (g : Var) : (nb078_alpha_dummy_369 g) ∈ (((Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0442 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0446 : (nb078_alpha_dummy_410) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_410))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0447 (g : Var) : (nb078_alpha_dummy_412 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0448 : (nb078_alpha_dummy_410) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0449 (g : Var) : (nb078_alpha_dummy_412 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0450 : (nb078_alpha_dummy_001) ∈ (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0451 (g : Var) : g ∈ (((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0452 : (nb078_alpha_dummy_001) ∈ (((syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0453 (g : Var) : g ∈ (((syn_ccom (Class.cv g) (syn_ccnv (Class.cv g)))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0454 : (nb078_alpha_dummy_001) ∈ (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
