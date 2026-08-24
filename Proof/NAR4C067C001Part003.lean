import NAR4C067C001Part002

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

noncomputable def nb067_alpha_dummy_300 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_301 : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv) 0)

noncomputable def nb067_alpha_dummy_302 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_303 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) 0)

noncomputable def nb067_alpha_dummy_304 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) 0)

noncomputable def nb067_alpha_dummy_305 : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_296)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_297)))).fv) 0)

noncomputable def nb067_alpha_dummy_306 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_299 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_300 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_307 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_296))).fv) 0)

noncomputable def nb067_alpha_dummy_308 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_299 f))).fv) 0)

noncomputable def nb067_alpha_dummy_309 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_297))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) 0)

noncomputable def nb067_alpha_dummy_310 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_300 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) 0)

noncomputable def nb067_alpha_dummy_311 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_312 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_313 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_282))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_314 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_315 : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv) 0)

noncomputable def nb067_alpha_dummy_316 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_317 : Var := (freshVar (((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_001)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_001)))).fv) 0)

noncomputable def nb067_alpha_dummy_318 (x : Var) (f : Var) : Var := (freshVar (((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv ∪ ((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv) 0)

noncomputable def nb067_alpha_dummy_319 : Var := (freshVar (((syn_crn (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((Class.cv (nb067_alpha_dummy_001))).fv) 0)

noncomputable def nb067_alpha_dummy_320 (x : Var) (f : Var) : Var := (freshVar (((syn_crn (Class.cv f))).fv ∪ ((Class.cv x)).fv) 0)

noncomputable def nb067_alpha_dummy_321 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb067_alpha_dummy_322 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb067_alpha_dummy_323 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb067_alpha_dummy_324 (f : Var) : Var := (freshVar (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb067_alpha_dummy_325 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) 0)

noncomputable def nb067_alpha_dummy_326 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) 1)

noncomputable def nb067_alpha_dummy_327 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) 0)

noncomputable def nb067_alpha_dummy_328 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) 1)

noncomputable def nb067_alpha_dummy_329 : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_330 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb067_alpha_dummy_331 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv) 0)

noncomputable def nb067_alpha_dummy_332 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv) 0)

noncomputable def nb067_alpha_dummy_333 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_326))).fv) 0)

noncomputable def nb067_alpha_dummy_334 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_326))).fv) 1)

noncomputable def nb067_alpha_dummy_335 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_328 f))).fv) 0)

noncomputable def nb067_alpha_dummy_336 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_328 f))).fv) 1)

noncomputable def nb067_alpha_dummy_337 : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_333))).fv) 0)

noncomputable def nb067_alpha_dummy_338 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_335 f))).fv) 0)

noncomputable def nb067_alpha_dummy_339 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_340 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_341 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_342 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb067_alpha_dummy_343 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb067_alpha_dummy_344 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb067_alpha_dummy_345 : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv) 0)

noncomputable def nb067_alpha_dummy_346 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_347 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) 0)

noncomputable def nb067_alpha_dummy_348 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) 0)

noncomputable def nb067_alpha_dummy_349 : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_340)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_341)))).fv) 0)

noncomputable def nb067_alpha_dummy_350 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb067_alpha_dummy_343 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_344 f)))).fv) 0)

noncomputable def nb067_alpha_dummy_351 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_340))).fv) 0)

noncomputable def nb067_alpha_dummy_352 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_343 f))).fv) 0)

noncomputable def nb067_alpha_dummy_353 : Var := (freshVar (((Class.cv (nb067_alpha_dummy_341))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) 0)

noncomputable def nb067_alpha_dummy_354 (f : Var) : Var := (freshVar (((Class.cv (nb067_alpha_dummy_344 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) 0)

noncomputable def nb067_alpha_dummy_355 : Var := (freshVar (((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_356 (f : Var) : Var := (freshVar (((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb067_alpha_dummy_357 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_326))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_358 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb067_alpha_dummy_359 : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv) 0)

noncomputable def nb067_alpha_dummy_360 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv) 0)

theorem nb067_fresh_000 : (nb067_alpha_dummy_073) ∉ (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_073] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_001 : (nb067_alpha_dummy_013) ∉ (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv) := by
  simpa only [nb067_alpha_dummy_013] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv) 0

theorem nb067_fresh_002 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_074 x y f) ∉ (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_074] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_003 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_014 x y f) ∉ (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv) := by
  simpa only [nb067_alpha_dummy_014] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv) 0

theorem nb067_fresh_004 : (nb067_alpha_dummy_021) ∉ (((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv) := by
  simpa only [nb067_alpha_dummy_021] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv) 0

theorem nb067_fresh_005 : (nb067_alpha_dummy_045) ∉ (((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_045] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_006 (x : Var) (y : Var) : (nb067_alpha_dummy_022 x y) ∉ (((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv) := by
  simpa only [nb067_alpha_dummy_022] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv) 0

theorem nb067_fresh_007 (x : Var) (y : Var) : (nb067_alpha_dummy_046 x y) ∉ (((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_046] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_008 : (nb067_alpha_dummy_097) ∉ (((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv) := by
  simpa only [nb067_alpha_dummy_097] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092))))))).fv) 0

theorem nb067_fresh_009 : (nb067_alpha_dummy_121) ∉ (((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_121] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_010 (f : Var) : (nb067_alpha_dummy_098 f) ∉ (((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv) := by
  simpa only [nb067_alpha_dummy_098] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))))).fv) 0

theorem nb067_fresh_011 (f : Var) : (nb067_alpha_dummy_122 f) ∉ (((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_122] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_012 : (nb067_alpha_dummy_133) ∉ (((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv) := by
  simpa only [nb067_alpha_dummy_133] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128))))))).fv) 0

theorem nb067_fresh_013 : (nb067_alpha_dummy_157) ∉ (((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_157] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_014 (f : Var) : (nb067_alpha_dummy_134 f) ∉ (((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv) := by
  simpa only [nb067_alpha_dummy_134] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))))).fv) 0

theorem nb067_fresh_015 (f : Var) : (nb067_alpha_dummy_158 f) ∉ (((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_158] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_016 : (nb067_alpha_dummy_175) ∉ (((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv) := by
  simpa only [nb067_alpha_dummy_175] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170))))))).fv) 0

theorem nb067_fresh_017 : (nb067_alpha_dummy_199) ∉ (((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_199] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_018 (f : Var) : (nb067_alpha_dummy_176 f) ∉ (((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv) := by
  simpa only [nb067_alpha_dummy_176] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))))).fv) 0

theorem nb067_fresh_019 (f : Var) : (nb067_alpha_dummy_200 f) ∉ (((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_200] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_020 : (nb067_alpha_dummy_235) ∉ (((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_235] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_021 : (nb067_alpha_dummy_211) ∉ (((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv) := by
  simpa only [nb067_alpha_dummy_211] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206))))))).fv) 0

theorem nb067_fresh_022 (f : Var) : (nb067_alpha_dummy_236 f) ∉ (((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_236] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_023 (f : Var) : (nb067_alpha_dummy_212 f) ∉ (((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv) := by
  simpa only [nb067_alpha_dummy_212] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))))).fv) 0

theorem nb067_fresh_024 : (nb067_alpha_dummy_271) ∉ (((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_271] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_025 : (nb067_alpha_dummy_247) ∉ (((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv) := by
  simpa only [nb067_alpha_dummy_247] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242))))))).fv) 0

theorem nb067_fresh_026 (f : Var) : (nb067_alpha_dummy_272 f) ∉ (((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_272] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_027 (f : Var) : (nb067_alpha_dummy_248 f) ∉ (((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv) := by
  simpa only [nb067_alpha_dummy_248] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))))).fv) 0

theorem nb067_fresh_028 : (nb067_alpha_dummy_311) ∉ (((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_311] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_029 : (nb067_alpha_dummy_287) ∉ (((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv) := by
  simpa only [nb067_alpha_dummy_287] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282))))))).fv) 0

theorem nb067_fresh_030 (f : Var) : (nb067_alpha_dummy_312 f) ∉ (((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_312] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_031 (f : Var) : (nb067_alpha_dummy_288 f) ∉ (((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv) := by
  simpa only [nb067_alpha_dummy_288] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))))).fv) 0

theorem nb067_fresh_032 : (nb067_alpha_dummy_355) ∉ (((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_355] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_033 : (nb067_alpha_dummy_331) ∉ (((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv) := by
  simpa only [nb067_alpha_dummy_331] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326))))))).fv) 0

theorem nb067_fresh_034 (f : Var) : (nb067_alpha_dummy_356 f) ∉ (((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb067_alpha_dummy_356] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb067_fresh_035 (f : Var) : (nb067_alpha_dummy_332 f) ∉ (((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv) := by
  simpa only [nb067_alpha_dummy_332] using freshVar_not_mem (((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))))).fv) 0

theorem nb067_fresh_036 : (nb067_alpha_dummy_163) ∉ (((Class.cv (nb067_alpha_dummy_000))).fv) := by
  simpa only [nb067_alpha_dummy_163] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv) 0

theorem nb067_fresh_037 : (nb067_alpha_dummy_164) ∉ (((Class.cv (nb067_alpha_dummy_000))).fv) := by
  simpa only [nb067_alpha_dummy_164] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv) 1

theorem nb067_distinct_038 : (nb067_alpha_dummy_163) ≠ (nb067_alpha_dummy_164) := by
  simpa only [nb067_alpha_dummy_163, nb067_alpha_dummy_164] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_039 : (nb067_alpha_dummy_083) ∉ (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) := by
  simpa only [nb067_alpha_dummy_083] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) 0

theorem nb067_fresh_040 : (nb067_alpha_dummy_084) ∉ (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) := by
  simpa only [nb067_alpha_dummy_084] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) 1

theorem nb067_fresh_041 : (nb067_alpha_dummy_085) ∉ (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) := by
  simpa only [nb067_alpha_dummy_085] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) 2

theorem nb067_distinct_042 : (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_084) := by
  simpa only [nb067_alpha_dummy_083, nb067_alpha_dummy_084] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_043 : (nb067_alpha_dummy_083) ≠ (nb067_alpha_dummy_085) := by
  simpa only [nb067_alpha_dummy_083, nb067_alpha_dummy_085] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_044 : (nb067_alpha_dummy_084) ≠ (nb067_alpha_dummy_085) := by
  simpa only [nb067_alpha_dummy_084, nb067_alpha_dummy_085] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_045 : (nb067_alpha_dummy_321) ∉ (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_321] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0

theorem nb067_fresh_046 : (nb067_alpha_dummy_322) ∉ (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_322] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1

theorem nb067_distinct_047 : (nb067_alpha_dummy_321) ≠ (nb067_alpha_dummy_322) := by
  simpa only [nb067_alpha_dummy_321, nb067_alpha_dummy_322] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_048 : (nb067_alpha_dummy_015) ∉ (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) := by
  simpa only [nb067_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) 0

theorem nb067_fresh_049 : (nb067_alpha_dummy_016) ∉ (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) := by
  simpa only [nb067_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) 1

theorem nb067_distinct_050 : (nb067_alpha_dummy_015) ≠ (nb067_alpha_dummy_016) := by
  simpa only [nb067_alpha_dummy_015, nb067_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_051 : (nb067_alpha_dummy_051) ∉ (((Class.cv (nb067_alpha_dummy_008))).fv) := by
  simpa only [nb067_alpha_dummy_051] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_008))).fv) 0

theorem nb067_fresh_052 : (nb067_alpha_dummy_052) ∉ (((Class.cv (nb067_alpha_dummy_008))).fv) := by
  simpa only [nb067_alpha_dummy_052] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_008))).fv) 1

theorem nb067_distinct_053 : (nb067_alpha_dummy_051) ≠ (nb067_alpha_dummy_052) := by
  simpa only [nb067_alpha_dummy_051, nb067_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_008))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_054 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_053 x y f) ∉ (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) := by
  simpa only [nb067_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) 0

theorem nb067_fresh_055 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_054 x y f) ∉ (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) := by
  simpa only [nb067_alpha_dummy_054] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) 1

theorem nb067_distinct_056 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_053 x y f) ≠ (nb067_alpha_dummy_054 x y f) := by
  simpa only [nb067_alpha_dummy_053, nb067_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_057 : (nb067_alpha_dummy_023) ∉ (((Class.cv (nb067_alpha_dummy_016))).fv) := by
  simpa only [nb067_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_016))).fv) 0

theorem nb067_fresh_058 : (nb067_alpha_dummy_024) ∉ (((Class.cv (nb067_alpha_dummy_016))).fv) := by
  simpa only [nb067_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_016))).fv) 1

theorem nb067_distinct_059 : (nb067_alpha_dummy_023) ≠ (nb067_alpha_dummy_024) := by
  simpa only [nb067_alpha_dummy_023, nb067_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_016))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_060 (x : Var) (y : Var) : (nb067_alpha_dummy_025 x y) ∉ (((Class.cv (nb067_alpha_dummy_018 x y))).fv) := by
  simpa only [nb067_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_018 x y))).fv) 0

theorem nb067_fresh_061 (x : Var) (y : Var) : (nb067_alpha_dummy_026 x y) ∉ (((Class.cv (nb067_alpha_dummy_018 x y))).fv) := by
  simpa only [nb067_alpha_dummy_026] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_018 x y))).fv) 1

theorem nb067_distinct_062 (x : Var) (y : Var) : (nb067_alpha_dummy_025 x y) ≠ (nb067_alpha_dummy_026 x y) := by
  simpa only [nb067_alpha_dummy_025, nb067_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_018 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_063 : (nb067_alpha_dummy_029) ∉ (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_064 : (nb067_alpha_dummy_030) ∉ (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_065 : (nb067_alpha_dummy_031) ∉ (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_066 : (nb067_alpha_dummy_029) ≠ (nb067_alpha_dummy_030) := by
  simpa only [nb067_alpha_dummy_029, nb067_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_067 : (nb067_alpha_dummy_029) ≠ (nb067_alpha_dummy_031) := by
  simpa only [nb067_alpha_dummy_029, nb067_alpha_dummy_031] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_068 : (nb067_alpha_dummy_030) ≠ (nb067_alpha_dummy_031) := by
  simpa only [nb067_alpha_dummy_030, nb067_alpha_dummy_031] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_069 (x : Var) (y : Var) : (nb067_alpha_dummy_032 x y) ∉ (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_070 (x : Var) (y : Var) : (nb067_alpha_dummy_033 x y) ∉ (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
