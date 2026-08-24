import NAR4C078C001Part002

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

noncomputable def nb078_alpha_dummy_300 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_301 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv) 0)

noncomputable def nb078_alpha_dummy_302 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_303 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_296))).fv) 0)

noncomputable def nb078_alpha_dummy_304 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_296))).fv) 1)

noncomputable def nb078_alpha_dummy_305 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_298 g))).fv) 0)

noncomputable def nb078_alpha_dummy_306 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_298 g))).fv) 1)

noncomputable def nb078_alpha_dummy_307 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_303)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_303)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_303))).fv) 0)

noncomputable def nb078_alpha_dummy_308 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_305 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_305 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_305 g))).fv) 0)

noncomputable def nb078_alpha_dummy_309 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_310 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_311 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_312 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_313 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_314 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_315 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv) 0)

noncomputable def nb078_alpha_dummy_316 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_317 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) 0)

noncomputable def nb078_alpha_dummy_318 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) 0)

noncomputable def nb078_alpha_dummy_319 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_310)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_311)))).fv) 0)

noncomputable def nb078_alpha_dummy_320 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_313 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_314 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_321 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_310))).fv) 0)

noncomputable def nb078_alpha_dummy_322 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_313 g))).fv) 0)

noncomputable def nb078_alpha_dummy_323 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_311))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) 0)

noncomputable def nb078_alpha_dummy_324 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_314 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) 0)

noncomputable def nb078_alpha_dummy_325 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_326 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_327 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_296))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_328 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_329 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv) 0)

noncomputable def nb078_alpha_dummy_330 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_331 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) 0)

noncomputable def nb078_alpha_dummy_332 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) 1)

noncomputable def nb078_alpha_dummy_333 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) 0)

noncomputable def nb078_alpha_dummy_334 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) 1)

noncomputable def nb078_alpha_dummy_335 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cphi (Class.cv (nb078_alpha_dummy_332)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_336 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_337 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv) 0)

noncomputable def nb078_alpha_dummy_338 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_339 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_332))).fv) 0)

noncomputable def nb078_alpha_dummy_340 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_332))).fv) 1)

noncomputable def nb078_alpha_dummy_341 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_334 g))).fv) 0)

noncomputable def nb078_alpha_dummy_342 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_334 g))).fv) 1)

noncomputable def nb078_alpha_dummy_343 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_339)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_339)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_339))).fv) 0)

noncomputable def nb078_alpha_dummy_344 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_341 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_341 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_341 g))).fv) 0)

noncomputable def nb078_alpha_dummy_345 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_346 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_347 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_348 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_349 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_350 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_351 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv) 0)

noncomputable def nb078_alpha_dummy_352 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_353 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) 0)

noncomputable def nb078_alpha_dummy_354 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) 0)

noncomputable def nb078_alpha_dummy_355 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_346)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_347)))).fv) 0)

noncomputable def nb078_alpha_dummy_356 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_349 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_350 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_357 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_346))).fv) 0)

noncomputable def nb078_alpha_dummy_358 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_349 g))).fv) 0)

noncomputable def nb078_alpha_dummy_359 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_347))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) 0)

noncomputable def nb078_alpha_dummy_360 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_350 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) 0)

noncomputable def nb078_alpha_dummy_361 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_331) (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_331)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_362 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_333 g) (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_363 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_332))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_364 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_365 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv) 0)

noncomputable def nb078_alpha_dummy_366 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_367 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv) 0)

noncomputable def nb078_alpha_dummy_368 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv) 1)

noncomputable def nb078_alpha_dummy_369 (g : Var) : Var := (freshVar (((Class.cv g)).fv) 0)

noncomputable def nb078_alpha_dummy_370 (g : Var) : Var := (freshVar (((Class.cv g)).fv) 1)

noncomputable def nb078_alpha_dummy_371 : Var := (freshVar (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_367)))).fv) 0)

noncomputable def nb078_alpha_dummy_372 (g : Var) : Var := (freshVar (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_369 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_373 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) 0)

noncomputable def nb078_alpha_dummy_374 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) 1)

noncomputable def nb078_alpha_dummy_375 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) 0)

noncomputable def nb078_alpha_dummy_376 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) 1)

noncomputable def nb078_alpha_dummy_377 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_378 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_379 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv) 0)

noncomputable def nb078_alpha_dummy_380 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_381 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_374))).fv) 0)

noncomputable def nb078_alpha_dummy_382 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_374))).fv) 1)

noncomputable def nb078_alpha_dummy_383 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_376 g))).fv) 0)

noncomputable def nb078_alpha_dummy_384 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_376 g))).fv) 1)

noncomputable def nb078_alpha_dummy_385 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_381)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_381)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_381))).fv) 0)

noncomputable def nb078_alpha_dummy_386 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_383 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_383 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_383 g))).fv) 0)

noncomputable def nb078_alpha_dummy_387 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_388 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_389 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_390 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_391 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_392 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_393 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv) 0)

noncomputable def nb078_alpha_dummy_394 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_395 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) 0)

noncomputable def nb078_alpha_dummy_396 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) 0)

noncomputable def nb078_alpha_dummy_397 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_388)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_389)))).fv) 0)

noncomputable def nb078_alpha_dummy_398 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_391 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_392 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_399 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_388))).fv) 0)

noncomputable def nb078_alpha_dummy_400 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_391 g))).fv) 0)

noncomputable def nb078_alpha_dummy_401 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_389))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) 0)

noncomputable def nb078_alpha_dummy_402 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_392 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) 0)

noncomputable def nb078_alpha_dummy_403 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_373) (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_373)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_404 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_375 g) (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_405 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_374))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_406 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_407 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv) 0)

noncomputable def nb078_alpha_dummy_408 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_409 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) 0)

noncomputable def nb078_alpha_dummy_410 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) 1)

noncomputable def nb078_alpha_dummy_411 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) 0)

noncomputable def nb078_alpha_dummy_412 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) 1)

noncomputable def nb078_alpha_dummy_413 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cphi (Class.cv (nb078_alpha_dummy_410)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_414 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_415 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv) 0)

noncomputable def nb078_alpha_dummy_416 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_417 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_410))).fv) 0)

noncomputable def nb078_alpha_dummy_418 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_410))).fv) 1)

noncomputable def nb078_alpha_dummy_419 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_412 g))).fv) 0)

noncomputable def nb078_alpha_dummy_420 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_412 g))).fv) 1)

noncomputable def nb078_alpha_dummy_421 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_417)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_417)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_417))).fv) 0)

noncomputable def nb078_alpha_dummy_422 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_419 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_419 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_419 g))).fv) 0)

noncomputable def nb078_alpha_dummy_423 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_424 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_425 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_426 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_427 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_428 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_429 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv) 0)

noncomputable def nb078_alpha_dummy_430 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_431 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) 0)

noncomputable def nb078_alpha_dummy_432 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) 0)

noncomputable def nb078_alpha_dummy_433 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_424)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_425)))).fv) 0)

noncomputable def nb078_alpha_dummy_434 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_427 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_428 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_435 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_424))).fv) 0)

noncomputable def nb078_alpha_dummy_436 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_427 g))).fv) 0)

noncomputable def nb078_alpha_dummy_437 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_425))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) 0)

noncomputable def nb078_alpha_dummy_438 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_428 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) 0)

noncomputable def nb078_alpha_dummy_439 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_409) (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367)) (Wff.classEq (Class.cv (nb078_alpha_dummy_409)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_440 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_411 g) (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_441 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_410))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_442 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_443 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv) 0)

noncomputable def nb078_alpha_dummy_444 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_445 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 0)

noncomputable def nb078_alpha_dummy_446 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 1)

noncomputable def nb078_alpha_dummy_447 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) 0)

noncomputable def nb078_alpha_dummy_448 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) 1)

noncomputable def nb078_alpha_dummy_449 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446))) (syn_csn (syn_c0c)))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
