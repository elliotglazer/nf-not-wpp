import NAR4C068C001Part002

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

noncomputable def nb068_alpha_dummy_300 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_297 f))).fv) 0)

noncomputable def nb068_alpha_dummy_301 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_302 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_303 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_304 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_305 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_306 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_307 : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv) 0)

noncomputable def nb068_alpha_dummy_308 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_309 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) 0)

noncomputable def nb068_alpha_dummy_310 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) 0)

noncomputable def nb068_alpha_dummy_311 : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_302)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_303)))).fv) 0)

noncomputable def nb068_alpha_dummy_312 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_305 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_306 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_313 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_302))).fv) 0)

noncomputable def nb068_alpha_dummy_314 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_305 f))).fv) 0)

noncomputable def nb068_alpha_dummy_315 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_303))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) 0)

noncomputable def nb068_alpha_dummy_316 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_306 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) 0)

noncomputable def nb068_alpha_dummy_317 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_318 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_319 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_288))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_320 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_321 : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv) 0)

noncomputable def nb068_alpha_dummy_322 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_323 : Var := (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv) 0)

noncomputable def nb068_alpha_dummy_324 (f : Var) : Var := (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f)))) (syn_cid))).fv) 0)

noncomputable def nb068_alpha_dummy_325 : Var := (freshVar (((syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb068_alpha_dummy_326 (f : Var) : Var := (freshVar (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb068_alpha_dummy_327 : Var := (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) 0)

noncomputable def nb068_alpha_dummy_328 : Var := (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) 1)

noncomputable def nb068_alpha_dummy_329 : Var := (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) 2)

noncomputable def nb068_alpha_dummy_330 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 0)

noncomputable def nb068_alpha_dummy_331 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 1)

noncomputable def nb068_alpha_dummy_332 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 2)

noncomputable def nb068_alpha_dummy_333 : Var := (freshVar (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327)) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_328)))))).fv) 0)

noncomputable def nb068_alpha_dummy_334 (f : Var) : Var := (freshVar (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_330 f)) (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_331 f)))))).fv) 0)

noncomputable def nb068_alpha_dummy_335 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) 0)

noncomputable def nb068_alpha_dummy_336 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) 1)

noncomputable def nb068_alpha_dummy_337 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) 0)

noncomputable def nb068_alpha_dummy_338 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) 1)

noncomputable def nb068_alpha_dummy_339 : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cphi (Class.cv (nb068_alpha_dummy_336)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_340 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_341 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv) 0)

noncomputable def nb068_alpha_dummy_342 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv) 0)

noncomputable def nb068_alpha_dummy_343 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_336))).fv) 0)

noncomputable def nb068_alpha_dummy_344 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_336))).fv) 1)

noncomputable def nb068_alpha_dummy_345 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_338 f))).fv) 0)

noncomputable def nb068_alpha_dummy_346 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_338 f))).fv) 1)

noncomputable def nb068_alpha_dummy_347 : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_343)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_343))).fv) 0)

noncomputable def nb068_alpha_dummy_348 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_345 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_345 f))).fv) 0)

noncomputable def nb068_alpha_dummy_349 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_350 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_351 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_352 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_353 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_354 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_355 : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv) 0)

noncomputable def nb068_alpha_dummy_356 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_353 f)) (Class.cv (nb068_alpha_dummy_354 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_353 f)) (Class.cv (nb068_alpha_dummy_354 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_357 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) 0)

noncomputable def nb068_alpha_dummy_358 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) 0)

noncomputable def nb068_alpha_dummy_359 : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_350)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_351)))).fv) 0)

noncomputable def nb068_alpha_dummy_360 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_353 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_354 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_361 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_350))).fv) 0)

noncomputable def nb068_alpha_dummy_362 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_353 f))).fv) 0)

noncomputable def nb068_alpha_dummy_363 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_351))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) 0)

noncomputable def nb068_alpha_dummy_364 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_354 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) 0)

noncomputable def nb068_alpha_dummy_365 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_366 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_367 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_336))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_368 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_369 : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv) 0)

noncomputable def nb068_alpha_dummy_370 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_371 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) 0)

noncomputable def nb068_alpha_dummy_372 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) 1)

noncomputable def nb068_alpha_dummy_373 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) 0)

noncomputable def nb068_alpha_dummy_374 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) 1)

noncomputable def nb068_alpha_dummy_375 : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cphi (Class.cv (nb068_alpha_dummy_372)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_376 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_377 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cphi (Class.cv (nb068_alpha_dummy_372))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cphi (Class.cv (nb068_alpha_dummy_372))))))).fv) 0)

noncomputable def nb068_alpha_dummy_378 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))))).fv) 0)

noncomputable def nb068_alpha_dummy_379 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_372))).fv) 0)

noncomputable def nb068_alpha_dummy_380 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_372))).fv) 1)

noncomputable def nb068_alpha_dummy_381 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_374 f))).fv) 0)

noncomputable def nb068_alpha_dummy_382 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_374 f))).fv) 1)

noncomputable def nb068_alpha_dummy_383 : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_379)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_379))).fv) 0)

noncomputable def nb068_alpha_dummy_384 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_381 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_381 f))).fv) 0)

noncomputable def nb068_alpha_dummy_385 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_386 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_387 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_388 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_389 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_390 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_391 : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv) 0)

noncomputable def nb068_alpha_dummy_392 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_393 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) 0)

noncomputable def nb068_alpha_dummy_394 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) 0)

noncomputable def nb068_alpha_dummy_395 : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_386)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_387)))).fv) 0)

noncomputable def nb068_alpha_dummy_396 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_389 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_390 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_397 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_386))).fv) 0)

noncomputable def nb068_alpha_dummy_398 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_389 f))).fv) 0)

noncomputable def nb068_alpha_dummy_399 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_387))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) 0)

noncomputable def nb068_alpha_dummy_400 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) 0)

noncomputable def nb068_alpha_dummy_401 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_402 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_403 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_372))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_404 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_405 : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv) 0)

noncomputable def nb068_alpha_dummy_406 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_407 : Var := (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 0)

noncomputable def nb068_alpha_dummy_408 : Var := (freshVar (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 1)

noncomputable def nb068_alpha_dummy_409 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv) 0)

noncomputable def nb068_alpha_dummy_410 (f : Var) : Var := (freshVar (((syn_ccnv (Class.cv f))).fv) 1)

noncomputable def nb068_alpha_dummy_411 : Var := (freshVar (({(nb068_alpha_dummy_407)} : Finset Var) ∪ ({(nb068_alpha_dummy_408)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_408)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_407)))).fv) 0)

noncomputable def nb068_alpha_dummy_412 (f : Var) : Var := (freshVar (({(nb068_alpha_dummy_409 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_410 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_409 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_413 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) 0)

noncomputable def nb068_alpha_dummy_414 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) 1)

noncomputable def nb068_alpha_dummy_415 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) 0)

noncomputable def nb068_alpha_dummy_416 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) 1)

noncomputable def nb068_alpha_dummy_417 : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cphi (Class.cv (nb068_alpha_dummy_414)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_418 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb068_alpha_dummy_419 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cphi (Class.cv (nb068_alpha_dummy_414))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cphi (Class.cv (nb068_alpha_dummy_414))))))).fv) 0)

noncomputable def nb068_alpha_dummy_420 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv) 0)

noncomputable def nb068_alpha_dummy_421 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_414))).fv) 0)

noncomputable def nb068_alpha_dummy_422 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_414))).fv) 1)

noncomputable def nb068_alpha_dummy_423 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_416 f))).fv) 0)

noncomputable def nb068_alpha_dummy_424 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_416 f))).fv) 1)

noncomputable def nb068_alpha_dummy_425 : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_421))).fv) 0)

noncomputable def nb068_alpha_dummy_426 (f : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_423 f))).fv) 0)

noncomputable def nb068_alpha_dummy_427 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_428 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_429 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_430 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb068_alpha_dummy_431 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb068_alpha_dummy_432 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb068_alpha_dummy_433 : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv) 0)

noncomputable def nb068_alpha_dummy_434 (f : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_435 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) 0)

noncomputable def nb068_alpha_dummy_436 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) 0)

noncomputable def nb068_alpha_dummy_437 : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_428)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_429)))).fv) 0)

noncomputable def nb068_alpha_dummy_438 (f : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb068_alpha_dummy_431 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_432 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_439 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_428))).fv) 0)

noncomputable def nb068_alpha_dummy_440 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_431 f))).fv) 0)

noncomputable def nb068_alpha_dummy_441 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_429))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) 0)

noncomputable def nb068_alpha_dummy_442 (f : Var) : Var := (freshVar (((Class.cv (nb068_alpha_dummy_432 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) 0)

noncomputable def nb068_alpha_dummy_443 : Var := (freshVar (((Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_444 (f : Var) : Var := (freshVar (((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb068_alpha_dummy_445 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_414))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_446 (f : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb068_alpha_dummy_447 : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv) 0)

noncomputable def nb068_alpha_dummy_448 (f : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv) 0)

noncomputable def nb068_alpha_dummy_449 : Var := (freshVar (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
