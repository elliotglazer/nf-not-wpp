import NAR4C090C001Part009

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

theorem nb090_distinct_392 (u : Var) : (nb090_alpha_dummy_308 u) ≠ (nb090_alpha_dummy_310 u) := by
  simpa only [nb090_alpha_dummy_308, nb090_alpha_dummy_310] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_393 (u : Var) : (nb090_alpha_dummy_309 u) ≠ (nb090_alpha_dummy_310 u) := by
  simpa only [nb090_alpha_dummy_309, nb090_alpha_dummy_310] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_394 (A : Class) : (nb090_alpha_dummy_317 A) ∉ (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_306 A))).fv) := by
  simpa only [nb090_alpha_dummy_317] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_306 A))).fv) 0

theorem nb090_fresh_395 (A : Class) : (nb090_alpha_dummy_313 A) ∉ (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) := by
  simpa only [nb090_alpha_dummy_313] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) 0

theorem nb090_fresh_396 (A : Class) : (nb090_alpha_dummy_319 A) ∉ (((Class.cv (nb090_alpha_dummy_307 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) := by
  simpa only [nb090_alpha_dummy_319] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_307 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) 0

theorem nb090_fresh_397 (u : Var) : (nb090_alpha_dummy_318 u) ∉ (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_309 u))).fv) := by
  simpa only [nb090_alpha_dummy_318] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_309 u))).fv) 0

theorem nb090_fresh_398 (u : Var) : (nb090_alpha_dummy_314 u) ∉ (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) := by
  simpa only [nb090_alpha_dummy_314] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) 0

theorem nb090_fresh_399 (u : Var) : (nb090_alpha_dummy_320 u) ∉ (((Class.cv (nb090_alpha_dummy_310 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) := by
  simpa only [nb090_alpha_dummy_320] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_310 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) 0

theorem nb090_fresh_400 (A : Class) : (nb090_alpha_dummy_337 A) ∉ (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) := by
  simpa only [nb090_alpha_dummy_337] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) 0

theorem nb090_fresh_401 (A : Class) : (nb090_alpha_dummy_338 A) ∉ (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) := by
  simpa only [nb090_alpha_dummy_338] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) 1

theorem nb090_distinct_402 (A : Class) : (nb090_alpha_dummy_337 A) ≠ (nb090_alpha_dummy_338 A) := by
  simpa only [nb090_alpha_dummy_337, nb090_alpha_dummy_338] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_403 (h : Var) : (nb090_alpha_dummy_339 h) ∉ (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) := by
  simpa only [nb090_alpha_dummy_339] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) 0

theorem nb090_fresh_404 (h : Var) : (nb090_alpha_dummy_340 h) ∉ (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) := by
  simpa only [nb090_alpha_dummy_340] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) 1

theorem nb090_distinct_405 (h : Var) : (nb090_alpha_dummy_339 h) ≠ (nb090_alpha_dummy_340 h) := by
  simpa only [nb090_alpha_dummy_339, nb090_alpha_dummy_340] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_406 (A : Class) : (nb090_alpha_dummy_345 A) ∉ (((Class.cv (nb090_alpha_dummy_338 A))).fv) := by
  simpa only [nb090_alpha_dummy_345] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_338 A))).fv) 0

theorem nb090_fresh_407 (A : Class) : (nb090_alpha_dummy_346 A) ∉ (((Class.cv (nb090_alpha_dummy_338 A))).fv) := by
  simpa only [nb090_alpha_dummy_346] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_338 A))).fv) 1

theorem nb090_distinct_408 (A : Class) : (nb090_alpha_dummy_345 A) ≠ (nb090_alpha_dummy_346 A) := by
  simpa only [nb090_alpha_dummy_345, nb090_alpha_dummy_346] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_338 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_409 (h : Var) : (nb090_alpha_dummy_347 h) ∉ (((Class.cv (nb090_alpha_dummy_340 h))).fv) := by
  simpa only [nb090_alpha_dummy_347] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_340 h))).fv) 0

theorem nb090_fresh_410 (h : Var) : (nb090_alpha_dummy_348 h) ∉ (((Class.cv (nb090_alpha_dummy_340 h))).fv) := by
  simpa only [nb090_alpha_dummy_348] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_340 h))).fv) 1

theorem nb090_distinct_411 (h : Var) : (nb090_alpha_dummy_347 h) ≠ (nb090_alpha_dummy_348 h) := by
  simpa only [nb090_alpha_dummy_347, nb090_alpha_dummy_348] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_340 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_412 (A : Class) : (nb090_alpha_dummy_351 A) ∉ (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_351] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_413 (A : Class) : (nb090_alpha_dummy_352 A) ∉ (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_352] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_414 (A : Class) : (nb090_alpha_dummy_353 A) ∉ (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_353] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_415 (A : Class) : (nb090_alpha_dummy_351 A) ≠ (nb090_alpha_dummy_352 A) := by
  simpa only [nb090_alpha_dummy_351, nb090_alpha_dummy_352] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_416 (A : Class) : (nb090_alpha_dummy_351 A) ≠ (nb090_alpha_dummy_353 A) := by
  simpa only [nb090_alpha_dummy_351, nb090_alpha_dummy_353] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_417 (A : Class) : (nb090_alpha_dummy_352 A) ≠ (nb090_alpha_dummy_353 A) := by
  simpa only [nb090_alpha_dummy_352, nb090_alpha_dummy_353] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_418 (h : Var) : (nb090_alpha_dummy_354 h) ∉ (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_354] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_419 (h : Var) : (nb090_alpha_dummy_355 h) ∉ (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_355] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_420 (h : Var) : (nb090_alpha_dummy_356 h) ∉ (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_356] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_421 (h : Var) : (nb090_alpha_dummy_354 h) ≠ (nb090_alpha_dummy_355 h) := by
  simpa only [nb090_alpha_dummy_354, nb090_alpha_dummy_355] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_422 (h : Var) : (nb090_alpha_dummy_354 h) ≠ (nb090_alpha_dummy_356 h) := by
  simpa only [nb090_alpha_dummy_354, nb090_alpha_dummy_356] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_423 (h : Var) : (nb090_alpha_dummy_355 h) ≠ (nb090_alpha_dummy_356 h) := by
  simpa only [nb090_alpha_dummy_355, nb090_alpha_dummy_356] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_424 (A : Class) : (nb090_alpha_dummy_363 A) ∉ (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_352 A))).fv) := by
  simpa only [nb090_alpha_dummy_363] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_352 A))).fv) 0

theorem nb090_fresh_425 (A : Class) : (nb090_alpha_dummy_359 A) ∉ (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) := by
  simpa only [nb090_alpha_dummy_359] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) 0

theorem nb090_fresh_426 (A : Class) : (nb090_alpha_dummy_365 A) ∉ (((Class.cv (nb090_alpha_dummy_353 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) := by
  simpa only [nb090_alpha_dummy_365] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_353 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) 0

theorem nb090_fresh_427 (h : Var) : (nb090_alpha_dummy_364 h) ∉ (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_355 h))).fv) := by
  simpa only [nb090_alpha_dummy_364] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_355 h))).fv) 0

theorem nb090_fresh_428 (h : Var) : (nb090_alpha_dummy_360 h) ∉ (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) := by
  simpa only [nb090_alpha_dummy_360] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) 0

theorem nb090_fresh_429 (h : Var) : (nb090_alpha_dummy_366 h) ∉ (((Class.cv (nb090_alpha_dummy_356 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) := by
  simpa only [nb090_alpha_dummy_366] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_356 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) 0

theorem nb090_fresh_430 (A : Class) : (nb090_alpha_dummy_417 A) ∉ (((Class.cv (nb090_alpha_dummy_375 A))).fv) := by
  simpa only [nb090_alpha_dummy_417] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_375 A))).fv) 0

theorem nb090_fresh_431 (v : Var) : (nb090_alpha_dummy_418 v) ∉ (((Class.cv (nb090_alpha_dummy_376 v))).fv) := by
  simpa only [nb090_alpha_dummy_418] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_376 v))).fv) 0

theorem nb090_fresh_432 (A : Class) : (nb090_alpha_dummy_389 A) ∉ (((Class.cv (nb090_alpha_dummy_382 A))).fv) := by
  simpa only [nb090_alpha_dummy_389] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_382 A))).fv) 0

theorem nb090_fresh_433 (A : Class) : (nb090_alpha_dummy_390 A) ∉ (((Class.cv (nb090_alpha_dummy_382 A))).fv) := by
  simpa only [nb090_alpha_dummy_390] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_382 A))).fv) 1

theorem nb090_distinct_434 (A : Class) : (nb090_alpha_dummy_389 A) ≠ (nb090_alpha_dummy_390 A) := by
  simpa only [nb090_alpha_dummy_389, nb090_alpha_dummy_390] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_382 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_435 (v : Var) : (nb090_alpha_dummy_391 v) ∉ (((Class.cv (nb090_alpha_dummy_384 v))).fv) := by
  simpa only [nb090_alpha_dummy_391] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_384 v))).fv) 0

theorem nb090_fresh_436 (v : Var) : (nb090_alpha_dummy_392 v) ∉ (((Class.cv (nb090_alpha_dummy_384 v))).fv) := by
  simpa only [nb090_alpha_dummy_392] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_384 v))).fv) 1

theorem nb090_distinct_437 (v : Var) : (nb090_alpha_dummy_391 v) ≠ (nb090_alpha_dummy_392 v) := by
  simpa only [nb090_alpha_dummy_391, nb090_alpha_dummy_392] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_384 v))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_438 (A : Class) : (nb090_alpha_dummy_395 A) ∉ (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_395] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_439 (A : Class) : (nb090_alpha_dummy_396 A) ∉ (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_396] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_440 (A : Class) : (nb090_alpha_dummy_397 A) ∉ (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_397] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_441 (A : Class) : (nb090_alpha_dummy_395 A) ≠ (nb090_alpha_dummy_396 A) := by
  simpa only [nb090_alpha_dummy_395, nb090_alpha_dummy_396] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_442 (A : Class) : (nb090_alpha_dummy_395 A) ≠ (nb090_alpha_dummy_397 A) := by
  simpa only [nb090_alpha_dummy_395, nb090_alpha_dummy_397] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_443 (A : Class) : (nb090_alpha_dummy_396 A) ≠ (nb090_alpha_dummy_397 A) := by
  simpa only [nb090_alpha_dummy_396, nb090_alpha_dummy_397] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_444 (v : Var) : (nb090_alpha_dummy_398 v) ∉ (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_398] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_445 (v : Var) : (nb090_alpha_dummy_399 v) ∉ (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_399] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_446 (v : Var) : (nb090_alpha_dummy_400 v) ∉ (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_400] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_447 (v : Var) : (nb090_alpha_dummy_398 v) ≠ (nb090_alpha_dummy_399 v) := by
  simpa only [nb090_alpha_dummy_398, nb090_alpha_dummy_399] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_448 (v : Var) : (nb090_alpha_dummy_398 v) ≠ (nb090_alpha_dummy_400 v) := by
  simpa only [nb090_alpha_dummy_398, nb090_alpha_dummy_400] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_449 (v : Var) : (nb090_alpha_dummy_399 v) ≠ (nb090_alpha_dummy_400 v) := by
  simpa only [nb090_alpha_dummy_399, nb090_alpha_dummy_400] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_450 (A : Class) : (nb090_alpha_dummy_407 A) ∉ (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_396 A))).fv) := by
  simpa only [nb090_alpha_dummy_407] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_396 A))).fv) 0

theorem nb090_fresh_451 (A : Class) : (nb090_alpha_dummy_403 A) ∉ (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) := by
  simpa only [nb090_alpha_dummy_403] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) 0

theorem nb090_fresh_452 (A : Class) : (nb090_alpha_dummy_409 A) ∉ (((Class.cv (nb090_alpha_dummy_397 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) := by
  simpa only [nb090_alpha_dummy_409] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_397 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) 0

theorem nb090_fresh_453 (v : Var) : (nb090_alpha_dummy_408 v) ∉ (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_399 v))).fv) := by
  simpa only [nb090_alpha_dummy_408] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_399 v))).fv) 0

theorem nb090_fresh_454 (v : Var) : (nb090_alpha_dummy_404 v) ∉ (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) := by
  simpa only [nb090_alpha_dummy_404] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) 0

theorem nb090_fresh_455 (v : Var) : (nb090_alpha_dummy_410 v) ∉ (((Class.cv (nb090_alpha_dummy_400 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) := by
  simpa only [nb090_alpha_dummy_410] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_400 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) 0

theorem nb090_fresh_456 (A : Class) : (nb090_alpha_dummy_431 A) ∉ (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) := by
  simpa only [nb090_alpha_dummy_431] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) 0

theorem nb090_fresh_457 (A : Class) : (nb090_alpha_dummy_432 A) ∉ (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) := by
  simpa only [nb090_alpha_dummy_432] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) 1

theorem nb090_distinct_458 (A : Class) : (nb090_alpha_dummy_431 A) ≠ (nb090_alpha_dummy_432 A) := by
  simpa only [nb090_alpha_dummy_431, nb090_alpha_dummy_432] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_459 (A : Class) : (nb090_alpha_dummy_467 A) ∉ (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) := by
  simpa only [nb090_alpha_dummy_467] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) 0

theorem nb090_fresh_460 (A : Class) : (nb090_alpha_dummy_468 A) ∉ (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) := by
  simpa only [nb090_alpha_dummy_468] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) 1

theorem nb090_distinct_461 (A : Class) : (nb090_alpha_dummy_467 A) ≠ (nb090_alpha_dummy_468 A) := by
  simpa only [nb090_alpha_dummy_467, nb090_alpha_dummy_468] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_462 (A : Class) : (nb090_alpha_dummy_581 A) ∉ (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) := by
  simpa only [nb090_alpha_dummy_581] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) 0

theorem nb090_fresh_463 (A : Class) : (nb090_alpha_dummy_582 A) ∉ (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) := by
  simpa only [nb090_alpha_dummy_582] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) 1

theorem nb090_distinct_464 (A : Class) : (nb090_alpha_dummy_581 A) ≠ (nb090_alpha_dummy_582 A) := by
  simpa only [nb090_alpha_dummy_581, nb090_alpha_dummy_582] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_465 (h : Var) : (nb090_alpha_dummy_433 h) ∉ (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) := by
  simpa only [nb090_alpha_dummy_433] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) 0

theorem nb090_fresh_466 (h : Var) : (nb090_alpha_dummy_434 h) ∉ (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) := by
  simpa only [nb090_alpha_dummy_434] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) 1

theorem nb090_distinct_467 (h : Var) : (nb090_alpha_dummy_433 h) ≠ (nb090_alpha_dummy_434 h) := by
  simpa only [nb090_alpha_dummy_433, nb090_alpha_dummy_434] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_468 (h : Var) : (nb090_alpha_dummy_469 h) ∉ (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) := by
  simpa only [nb090_alpha_dummy_469] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) 0

theorem nb090_fresh_469 (h : Var) : (nb090_alpha_dummy_470 h) ∉ (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) := by
  simpa only [nb090_alpha_dummy_470] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) 1

theorem nb090_distinct_470 (h : Var) : (nb090_alpha_dummy_469 h) ≠ (nb090_alpha_dummy_470 h) := by
  simpa only [nb090_alpha_dummy_469, nb090_alpha_dummy_470] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_471 (h : Var) : (nb090_alpha_dummy_583 h) ∉ (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) := by
  simpa only [nb090_alpha_dummy_583] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) 0

theorem nb090_fresh_472 (h : Var) : (nb090_alpha_dummy_584 h) ∉ (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) := by
  simpa only [nb090_alpha_dummy_584] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) 1

theorem nb090_distinct_473 (h : Var) : (nb090_alpha_dummy_583 h) ≠ (nb090_alpha_dummy_584 h) := by
  simpa only [nb090_alpha_dummy_583, nb090_alpha_dummy_584] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_474 (A : Class) : (nb090_alpha_dummy_439 A) ∉ (((Class.cv (nb090_alpha_dummy_432 A))).fv) := by
  simpa only [nb090_alpha_dummy_439] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_432 A))).fv) 0

theorem nb090_fresh_475 (A : Class) : (nb090_alpha_dummy_440 A) ∉ (((Class.cv (nb090_alpha_dummy_432 A))).fv) := by
  simpa only [nb090_alpha_dummy_440] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_432 A))).fv) 1

theorem nb090_distinct_476 (A : Class) : (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_440 A) := by
  simpa only [nb090_alpha_dummy_439, nb090_alpha_dummy_440] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_432 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_477 (h : Var) : (nb090_alpha_dummy_441 h) ∉ (((Class.cv (nb090_alpha_dummy_434 h))).fv) := by
  simpa only [nb090_alpha_dummy_441] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_434 h))).fv) 0

theorem nb090_fresh_478 (h : Var) : (nb090_alpha_dummy_442 h) ∉ (((Class.cv (nb090_alpha_dummy_434 h))).fv) := by
  simpa only [nb090_alpha_dummy_442] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_434 h))).fv) 1

theorem nb090_distinct_479 (h : Var) : (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_442 h) := by
  simpa only [nb090_alpha_dummy_441, nb090_alpha_dummy_442] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_434 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_480 (A : Class) : (nb090_alpha_dummy_445 A) ∉ (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_445] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_481 (A : Class) : (nb090_alpha_dummy_446 A) ∉ (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_446] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_482 (A : Class) : (nb090_alpha_dummy_447 A) ∉ (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_447] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_483 (A : Class) : (nb090_alpha_dummy_445 A) ≠ (nb090_alpha_dummy_446 A) := by
  simpa only [nb090_alpha_dummy_445, nb090_alpha_dummy_446] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_484 (A : Class) : (nb090_alpha_dummy_445 A) ≠ (nb090_alpha_dummy_447 A) := by
  simpa only [nb090_alpha_dummy_445, nb090_alpha_dummy_447] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_485 (A : Class) : (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_447 A) := by
  simpa only [nb090_alpha_dummy_446, nb090_alpha_dummy_447] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_486 (h : Var) : (nb090_alpha_dummy_448 h) ∉ (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_448] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_487 (h : Var) : (nb090_alpha_dummy_449 h) ∉ (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_449] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_488 (h : Var) : (nb090_alpha_dummy_450 h) ∉ (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_450] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_489 (h : Var) : (nb090_alpha_dummy_448 h) ≠ (nb090_alpha_dummy_449 h) := by
  simpa only [nb090_alpha_dummy_448, nb090_alpha_dummy_449] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_490 (h : Var) : (nb090_alpha_dummy_448 h) ≠ (nb090_alpha_dummy_450 h) := by
  simpa only [nb090_alpha_dummy_448, nb090_alpha_dummy_450] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_491 (h : Var) : (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_450 h) := by
  simpa only [nb090_alpha_dummy_449, nb090_alpha_dummy_450] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_492 (A : Class) : (nb090_alpha_dummy_457 A) ∉ (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_446 A))).fv) := by
  simpa only [nb090_alpha_dummy_457] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_446 A))).fv) 0

theorem nb090_fresh_493 (A : Class) : (nb090_alpha_dummy_453 A) ∉ (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) := by
  simpa only [nb090_alpha_dummy_453] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) 0

theorem nb090_fresh_494 (A : Class) : (nb090_alpha_dummy_459 A) ∉ (((Class.cv (nb090_alpha_dummy_447 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) := by
  simpa only [nb090_alpha_dummy_459] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_447 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) 0

theorem nb090_fresh_495 (h : Var) : (nb090_alpha_dummy_458 h) ∉ (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_449 h))).fv) := by
  simpa only [nb090_alpha_dummy_458] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_449 h))).fv) 0

theorem nb090_fresh_496 (h : Var) : (nb090_alpha_dummy_454 h) ∉ (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) := by
  simpa only [nb090_alpha_dummy_454] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) 0

theorem nb090_fresh_497 (h : Var) : (nb090_alpha_dummy_460 h) ∉ (((Class.cv (nb090_alpha_dummy_450 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) := by
  simpa only [nb090_alpha_dummy_460] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_450 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) 0

theorem nb090_fresh_498 (A : Class) : (nb090_alpha_dummy_475 A) ∉ (((Class.cv (nb090_alpha_dummy_468 A))).fv) := by
  simpa only [nb090_alpha_dummy_475] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_468 A))).fv) 0

theorem nb090_fresh_499 (A : Class) : (nb090_alpha_dummy_476 A) ∉ (((Class.cv (nb090_alpha_dummy_468 A))).fv) := by
  simpa only [nb090_alpha_dummy_476] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_468 A))).fv) 1

theorem nb090_distinct_500 (A : Class) : (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_476 A) := by
  simpa only [nb090_alpha_dummy_475, nb090_alpha_dummy_476] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_468 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_501 (h : Var) : (nb090_alpha_dummy_477 h) ∉ (((Class.cv (nb090_alpha_dummy_470 h))).fv) := by
  simpa only [nb090_alpha_dummy_477] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_470 h))).fv) 0

theorem nb090_fresh_502 (h : Var) : (nb090_alpha_dummy_478 h) ∉ (((Class.cv (nb090_alpha_dummy_470 h))).fv) := by
  simpa only [nb090_alpha_dummy_478] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_470 h))).fv) 1

theorem nb090_distinct_503 (h : Var) : (nb090_alpha_dummy_477 h) ≠ (nb090_alpha_dummy_478 h) := by
  simpa only [nb090_alpha_dummy_477, nb090_alpha_dummy_478] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_470 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_504 (A : Class) : (nb090_alpha_dummy_481 A) ∉ (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_481] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_505 (A : Class) : (nb090_alpha_dummy_482 A) ∉ (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_482] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_506 (A : Class) : (nb090_alpha_dummy_483 A) ∉ (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_483] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_507 (A : Class) : (nb090_alpha_dummy_481 A) ≠ (nb090_alpha_dummy_482 A) := by
  simpa only [nb090_alpha_dummy_481, nb090_alpha_dummy_482] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_508 (A : Class) : (nb090_alpha_dummy_481 A) ≠ (nb090_alpha_dummy_483 A) := by
  simpa only [nb090_alpha_dummy_481, nb090_alpha_dummy_483] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_509 (A : Class) : (nb090_alpha_dummy_482 A) ≠ (nb090_alpha_dummy_483 A) := by
  simpa only [nb090_alpha_dummy_482, nb090_alpha_dummy_483] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_510 (h : Var) : (nb090_alpha_dummy_484 h) ∉ (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_484] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_511 (h : Var) : (nb090_alpha_dummy_485 h) ∉ (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_485] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_512 (h : Var) : (nb090_alpha_dummy_486 h) ∉ (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_486] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_513 (h : Var) : (nb090_alpha_dummy_484 h) ≠ (nb090_alpha_dummy_485 h) := by
  simpa only [nb090_alpha_dummy_484, nb090_alpha_dummy_485] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_514 (h : Var) : (nb090_alpha_dummy_484 h) ≠ (nb090_alpha_dummy_486 h) := by
  simpa only [nb090_alpha_dummy_484, nb090_alpha_dummy_486] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_515 (h : Var) : (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_486 h) := by
  simpa only [nb090_alpha_dummy_485, nb090_alpha_dummy_486] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_516 (A : Class) : (nb090_alpha_dummy_493 A) ∉ (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_482 A))).fv) := by
  simpa only [nb090_alpha_dummy_493] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_482 A))).fv) 0

theorem nb090_fresh_517 (A : Class) : (nb090_alpha_dummy_489 A) ∉ (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) := by
  simpa only [nb090_alpha_dummy_489] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) 0

theorem nb090_fresh_518 (A : Class) : (nb090_alpha_dummy_495 A) ∉ (((Class.cv (nb090_alpha_dummy_483 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) := by
  simpa only [nb090_alpha_dummy_495] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_483 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) 0

theorem nb090_fresh_519 (h : Var) : (nb090_alpha_dummy_494 h) ∉ (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_485 h))).fv) := by
  simpa only [nb090_alpha_dummy_494] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_485 h))).fv) 0

theorem nb090_fresh_520 (h : Var) : (nb090_alpha_dummy_490 h) ∉ (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) := by
  simpa only [nb090_alpha_dummy_490] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) 0

theorem nb090_fresh_521 (h : Var) : (nb090_alpha_dummy_496 h) ∉ (((Class.cv (nb090_alpha_dummy_486 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) := by
  simpa only [nb090_alpha_dummy_496] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_486 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) 0

theorem nb090_fresh_522 (A : Class) : (nb090_alpha_dummy_509 A) ∉ (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) := by
  simpa only [nb090_alpha_dummy_509] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) 0

theorem nb090_fresh_523 (A : Class) : (nb090_alpha_dummy_510 A) ∉ (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) := by
  simpa only [nb090_alpha_dummy_510] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) 1

theorem nb090_distinct_524 (A : Class) : (nb090_alpha_dummy_509 A) ≠ (nb090_alpha_dummy_510 A) := by
  simpa only [nb090_alpha_dummy_509, nb090_alpha_dummy_510] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_525 (A : Class) : (nb090_alpha_dummy_545 A) ∉ (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) := by
  simpa only [nb090_alpha_dummy_545] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) 0

theorem nb090_fresh_526 (A : Class) : (nb090_alpha_dummy_546 A) ∉ (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) := by
  simpa only [nb090_alpha_dummy_546] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) 1

theorem nb090_distinct_527 (A : Class) : (nb090_alpha_dummy_545 A) ≠ (nb090_alpha_dummy_546 A) := by
  simpa only [nb090_alpha_dummy_545, nb090_alpha_dummy_546] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_528 (h : Var) : (nb090_alpha_dummy_511 h) ∉ (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) := by
  simpa only [nb090_alpha_dummy_511] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) 0

theorem nb090_fresh_529 (h : Var) : (nb090_alpha_dummy_512 h) ∉ (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) := by
  simpa only [nb090_alpha_dummy_512] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) 1

theorem nb090_distinct_530 (h : Var) : (nb090_alpha_dummy_511 h) ≠ (nb090_alpha_dummy_512 h) := by
  simpa only [nb090_alpha_dummy_511, nb090_alpha_dummy_512] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_531 (h : Var) : (nb090_alpha_dummy_547 h) ∉ (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) := by
  simpa only [nb090_alpha_dummy_547] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) 0

theorem nb090_fresh_532 (h : Var) : (nb090_alpha_dummy_548 h) ∉ (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) := by
  simpa only [nb090_alpha_dummy_548] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) 1

theorem nb090_distinct_533 (h : Var) : (nb090_alpha_dummy_547 h) ≠ (nb090_alpha_dummy_548 h) := by
  simpa only [nb090_alpha_dummy_547, nb090_alpha_dummy_548] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_534 (A : Class) : (nb090_alpha_dummy_517 A) ∉ (((Class.cv (nb090_alpha_dummy_510 A))).fv) := by
  simpa only [nb090_alpha_dummy_517] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_510 A))).fv) 0

theorem nb090_fresh_535 (A : Class) : (nb090_alpha_dummy_518 A) ∉ (((Class.cv (nb090_alpha_dummy_510 A))).fv) := by
  simpa only [nb090_alpha_dummy_518] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_510 A))).fv) 1

theorem nb090_distinct_536 (A : Class) : (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_518 A) := by
  simpa only [nb090_alpha_dummy_517, nb090_alpha_dummy_518] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_510 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_537 (h : Var) : (nb090_alpha_dummy_519 h) ∉ (((Class.cv (nb090_alpha_dummy_512 h))).fv) := by
  simpa only [nb090_alpha_dummy_519] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_512 h))).fv) 0

theorem nb090_fresh_538 (h : Var) : (nb090_alpha_dummy_520 h) ∉ (((Class.cv (nb090_alpha_dummy_512 h))).fv) := by
  simpa only [nb090_alpha_dummy_520] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_512 h))).fv) 1

theorem nb090_distinct_539 (h : Var) : (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_520 h) := by
  simpa only [nb090_alpha_dummy_519, nb090_alpha_dummy_520] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_512 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_540 (A : Class) : (nb090_alpha_dummy_523 A) ∉ (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_523] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_541 (A : Class) : (nb090_alpha_dummy_524 A) ∉ (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_524] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
