import NAR4C090C001Part002

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

noncomputable def nb090_alpha_dummy_300 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_292 A))).fv) 1)

noncomputable def nb090_alpha_dummy_301 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_294 u))).fv) 0)

noncomputable def nb090_alpha_dummy_302 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_294 u))).fv) 1)

noncomputable def nb090_alpha_dummy_303 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_299 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_299 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_299 A))).fv) 0)

noncomputable def nb090_alpha_dummy_304 (u : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_301 u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_301 u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_301 u))).fv) 0)

noncomputable def nb090_alpha_dummy_305 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_306 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_307 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_308 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_309 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_310 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_311 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_312 (u : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv) 0)

noncomputable def nb090_alpha_dummy_313 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) 0)

noncomputable def nb090_alpha_dummy_314 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) 0)

noncomputable def nb090_alpha_dummy_315 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_306 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_307 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_316 (u : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_309 u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_310 u)))).fv) 0)

noncomputable def nb090_alpha_dummy_317 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_306 A))).fv) 0)

noncomputable def nb090_alpha_dummy_318 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_309 u))).fv) 0)

noncomputable def nb090_alpha_dummy_319 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_307 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) 0)

noncomputable def nb090_alpha_dummy_320 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_310 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) 0)

noncomputable def nb090_alpha_dummy_321 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_291 A) (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_322 (u : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_323 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_324 (u : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_325 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_326 (u : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv) 0)

noncomputable def nb090_alpha_dummy_327 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_285 A))).fv) 0)

noncomputable def nb090_alpha_dummy_328 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_286 u))).fv) 0)

noncomputable def nb090_alpha_dummy_329 (A : Class) : Var := (freshVar (((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv) 0)

noncomputable def nb090_alpha_dummy_330 (v : Var) (h : Var) : Var := (freshVar (((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv ∪ ((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv) 0)

noncomputable def nb090_alpha_dummy_331 (A : Class) : Var := (freshVar (((syn_crn (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_332 (v : Var) (h : Var) : Var := (freshVar (((syn_crn (Class.cv h))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) 0)

noncomputable def nb090_alpha_dummy_333 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb090_alpha_dummy_334 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb090_alpha_dummy_335 (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb090_alpha_dummy_336 (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb090_alpha_dummy_337 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) 0)

noncomputable def nb090_alpha_dummy_338 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) 1)

noncomputable def nb090_alpha_dummy_339 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) 0)

noncomputable def nb090_alpha_dummy_340 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) 1)

noncomputable def nb090_alpha_dummy_341 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_342 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_343 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_344 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_345 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_338 A))).fv) 0)

noncomputable def nb090_alpha_dummy_346 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_338 A))).fv) 1)

noncomputable def nb090_alpha_dummy_347 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_340 h))).fv) 0)

noncomputable def nb090_alpha_dummy_348 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_340 h))).fv) 1)

noncomputable def nb090_alpha_dummy_349 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_345 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_345 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_345 A))).fv) 0)

noncomputable def nb090_alpha_dummy_350 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_347 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_347 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_347 h))).fv) 0)

noncomputable def nb090_alpha_dummy_351 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_352 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_353 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_354 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_355 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_356 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_357 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_358 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_359 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) 0)

noncomputable def nb090_alpha_dummy_360 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) 0)

noncomputable def nb090_alpha_dummy_361 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_352 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_353 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_362 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_355 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_356 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_363 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_352 A))).fv) 0)

noncomputable def nb090_alpha_dummy_364 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_355 h))).fv) 0)

noncomputable def nb090_alpha_dummy_365 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_353 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) 0)

noncomputable def nb090_alpha_dummy_366 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_356 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) 0)

noncomputable def nb090_alpha_dummy_367 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_368 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_369 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_370 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_371 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_372 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_373 (A : Class) : Var := (freshVar (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0)

noncomputable def nb090_alpha_dummy_374 (v : Var) : Var := (freshVar (((syn_c2nd)).fv ∪ ((Class.cv v)).fv) 0)

noncomputable def nb090_alpha_dummy_375 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_373 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_373 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_376 (v : Var) : Var := (freshVar (({(nb090_alpha_dummy_374 v)} : Finset Var) ∪ ((syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))).fv) 0)

noncomputable def nb090_alpha_dummy_377 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_373 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_373 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv) 0)

noncomputable def nb090_alpha_dummy_378 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_373 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_373 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv) 1)

noncomputable def nb090_alpha_dummy_379 (v : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_374 v) (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv) 0)

noncomputable def nb090_alpha_dummy_380 (v : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_374 v) (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv) 1)

noncomputable def nb090_alpha_dummy_381 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) 0)

noncomputable def nb090_alpha_dummy_382 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) 1)

noncomputable def nb090_alpha_dummy_383 (v : Var) : Var := (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) 0)

noncomputable def nb090_alpha_dummy_384 (v : Var) : Var := (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) 1)

noncomputable def nb090_alpha_dummy_385 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_386 (v : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_387 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_388 (v : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv) 0)

noncomputable def nb090_alpha_dummy_389 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_382 A))).fv) 0)

noncomputable def nb090_alpha_dummy_390 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_382 A))).fv) 1)

noncomputable def nb090_alpha_dummy_391 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_384 v))).fv) 0)

noncomputable def nb090_alpha_dummy_392 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_384 v))).fv) 1)

noncomputable def nb090_alpha_dummy_393 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_389 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_389 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_389 A))).fv) 0)

noncomputable def nb090_alpha_dummy_394 (v : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_391 v)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_391 v)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_391 v))).fv) 0)

noncomputable def nb090_alpha_dummy_395 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_396 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_397 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_398 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_399 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_400 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_401 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_402 (v : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv) 0)

noncomputable def nb090_alpha_dummy_403 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) 0)

noncomputable def nb090_alpha_dummy_404 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) 0)

noncomputable def nb090_alpha_dummy_405 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_396 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_397 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_406 (v : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_399 v)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_400 v)))).fv) 0)

noncomputable def nb090_alpha_dummy_407 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_396 A))).fv) 0)

noncomputable def nb090_alpha_dummy_408 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_399 v))).fv) 0)

noncomputable def nb090_alpha_dummy_409 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_397 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) 0)

noncomputable def nb090_alpha_dummy_410 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_400 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) 0)

noncomputable def nb090_alpha_dummy_411 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_412 (v : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_413 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_414 (v : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_415 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_416 (v : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv) 0)

noncomputable def nb090_alpha_dummy_417 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_375 A))).fv) 0)

noncomputable def nb090_alpha_dummy_418 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_376 v))).fv) 0)

noncomputable def nb090_alpha_dummy_419 (A : Class) : Var := (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv) 0)

noncomputable def nb090_alpha_dummy_420 (h : Var) : Var := (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv) 0)

noncomputable def nb090_alpha_dummy_421 (A : Class) : Var := (freshVar (((syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb090_alpha_dummy_422 (h : Var) : Var := (freshVar (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb090_alpha_dummy_423 (A : Class) : Var := (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) 0)

noncomputable def nb090_alpha_dummy_424 (A : Class) : Var := (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) 1)

noncomputable def nb090_alpha_dummy_425 (A : Class) : Var := (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) 2)

noncomputable def nb090_alpha_dummy_426 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 0)

noncomputable def nb090_alpha_dummy_427 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 1)

noncomputable def nb090_alpha_dummy_428 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 2)

noncomputable def nb090_alpha_dummy_429 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_423 A)) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (Class.cv (nb090_alpha_dummy_425 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_425 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_424 A)))))).fv) 0)

noncomputable def nb090_alpha_dummy_430 (h : Var) : Var := (freshVar (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_426 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_427 h)))))).fv) 0)

noncomputable def nb090_alpha_dummy_431 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) 0)

noncomputable def nb090_alpha_dummy_432 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) 1)

noncomputable def nb090_alpha_dummy_433 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) 0)

noncomputable def nb090_alpha_dummy_434 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) 1)

noncomputable def nb090_alpha_dummy_435 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_436 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_437 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_438 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_439 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_432 A))).fv) 0)

noncomputable def nb090_alpha_dummy_440 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_432 A))).fv) 1)

noncomputable def nb090_alpha_dummy_441 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_434 h))).fv) 0)

noncomputable def nb090_alpha_dummy_442 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_434 h))).fv) 1)

noncomputable def nb090_alpha_dummy_443 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_439 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_439 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_439 A))).fv) 0)

noncomputable def nb090_alpha_dummy_444 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_441 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_441 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_441 h))).fv) 0)

noncomputable def nb090_alpha_dummy_445 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_446 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_447 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_448 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_449 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
