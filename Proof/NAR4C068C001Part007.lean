import NAR4C068C001Part006

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

theorem nb068_fresh_342 (f : Var) : (nb068_alpha_dummy_364 f) ∉ (((Class.cv (nb068_alpha_dummy_354 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) := by
  simpa only [nb068_alpha_dummy_364] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_354 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) 0

theorem nb068_fresh_343 : (nb068_alpha_dummy_379) ∉ (((Class.cv (nb068_alpha_dummy_372))).fv) := by
  simpa only [nb068_alpha_dummy_379] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_372))).fv) 0

theorem nb068_fresh_344 : (nb068_alpha_dummy_380) ∉ (((Class.cv (nb068_alpha_dummy_372))).fv) := by
  simpa only [nb068_alpha_dummy_380] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_372))).fv) 1

theorem nb068_distinct_345 : (nb068_alpha_dummy_379) ≠ (nb068_alpha_dummy_380) := by
  simpa only [nb068_alpha_dummy_379, nb068_alpha_dummy_380] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_372))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_346 (f : Var) : (nb068_alpha_dummy_381 f) ∉ (((Class.cv (nb068_alpha_dummy_374 f))).fv) := by
  simpa only [nb068_alpha_dummy_381] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_374 f))).fv) 0

theorem nb068_fresh_347 (f : Var) : (nb068_alpha_dummy_382 f) ∉ (((Class.cv (nb068_alpha_dummy_374 f))).fv) := by
  simpa only [nb068_alpha_dummy_382] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_374 f))).fv) 1

theorem nb068_distinct_348 (f : Var) : (nb068_alpha_dummy_381 f) ≠ (nb068_alpha_dummy_382 f) := by
  simpa only [nb068_alpha_dummy_381, nb068_alpha_dummy_382] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_374 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_349 : (nb068_alpha_dummy_385) ∉ (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_385] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_350 : (nb068_alpha_dummy_386) ∉ (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_386] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_351 : (nb068_alpha_dummy_387) ∉ (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_387] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_352 : (nb068_alpha_dummy_385) ≠ (nb068_alpha_dummy_386) := by
  simpa only [nb068_alpha_dummy_385, nb068_alpha_dummy_386] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_353 : (nb068_alpha_dummy_385) ≠ (nb068_alpha_dummy_387) := by
  simpa only [nb068_alpha_dummy_385, nb068_alpha_dummy_387] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_354 : (nb068_alpha_dummy_386) ≠ (nb068_alpha_dummy_387) := by
  simpa only [nb068_alpha_dummy_386, nb068_alpha_dummy_387] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_355 (f : Var) : (nb068_alpha_dummy_388 f) ∉ (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_388] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_356 (f : Var) : (nb068_alpha_dummy_389 f) ∉ (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_389] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_357 (f : Var) : (nb068_alpha_dummy_390 f) ∉ (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_390] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_358 (f : Var) : (nb068_alpha_dummy_388 f) ≠ (nb068_alpha_dummy_389 f) := by
  simpa only [nb068_alpha_dummy_388, nb068_alpha_dummy_389] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_359 (f : Var) : (nb068_alpha_dummy_388 f) ≠ (nb068_alpha_dummy_390 f) := by
  simpa only [nb068_alpha_dummy_388, nb068_alpha_dummy_390] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_360 (f : Var) : (nb068_alpha_dummy_389 f) ≠ (nb068_alpha_dummy_390 f) := by
  simpa only [nb068_alpha_dummy_389, nb068_alpha_dummy_390] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_361 : (nb068_alpha_dummy_397) ∉ (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_386))).fv) := by
  simpa only [nb068_alpha_dummy_397] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_386))).fv) 0

theorem nb068_fresh_362 : (nb068_alpha_dummy_393) ∉ (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) := by
  simpa only [nb068_alpha_dummy_393] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_386))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) 0

theorem nb068_fresh_363 : (nb068_alpha_dummy_399) ∉ (((Class.cv (nb068_alpha_dummy_387))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) := by
  simpa only [nb068_alpha_dummy_399] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_387))).fv ∪ ((Class.cv (nb068_alpha_dummy_387))).fv) 0

theorem nb068_fresh_364 (f : Var) : (nb068_alpha_dummy_398 f) ∉ (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_389 f))).fv) := by
  simpa only [nb068_alpha_dummy_398] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_389 f))).fv) 0

theorem nb068_fresh_365 (f : Var) : (nb068_alpha_dummy_394 f) ∉ (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) := by
  simpa only [nb068_alpha_dummy_394] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_389 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) 0

theorem nb068_fresh_366 (f : Var) : (nb068_alpha_dummy_400 f) ∉ (((Class.cv (nb068_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) := by
  simpa only [nb068_alpha_dummy_400] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_390 f))).fv) 0

theorem nb068_fresh_367 : (nb068_alpha_dummy_413) ∉ (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) := by
  simpa only [nb068_alpha_dummy_413] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) 0

theorem nb068_fresh_368 : (nb068_alpha_dummy_414) ∉ (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) := by
  simpa only [nb068_alpha_dummy_414] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) 1

theorem nb068_distinct_369 : (nb068_alpha_dummy_413) ≠ (nb068_alpha_dummy_414) := by
  simpa only [nb068_alpha_dummy_413, nb068_alpha_dummy_414] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_370 : (nb068_alpha_dummy_449) ∉ (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) := by
  simpa only [nb068_alpha_dummy_449] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) 0

theorem nb068_fresh_371 : (nb068_alpha_dummy_450) ∉ (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) := by
  simpa only [nb068_alpha_dummy_450] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) 1

theorem nb068_distinct_372 : (nb068_alpha_dummy_449) ≠ (nb068_alpha_dummy_450) := by
  simpa only [nb068_alpha_dummy_449, nb068_alpha_dummy_450] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_408))).fv ∪ ((Class.cv (nb068_alpha_dummy_407))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_373 (f : Var) : (nb068_alpha_dummy_415 f) ∉ (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) := by
  simpa only [nb068_alpha_dummy_415] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) 0

theorem nb068_fresh_374 (f : Var) : (nb068_alpha_dummy_416 f) ∉ (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) := by
  simpa only [nb068_alpha_dummy_416] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) 1

theorem nb068_distinct_375 (f : Var) : (nb068_alpha_dummy_415 f) ≠ (nb068_alpha_dummy_416 f) := by
  simpa only [nb068_alpha_dummy_415, nb068_alpha_dummy_416] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_376 (f : Var) : (nb068_alpha_dummy_451 f) ∉ (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv) := by
  simpa only [nb068_alpha_dummy_451] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv) 0

theorem nb068_fresh_377 (f : Var) : (nb068_alpha_dummy_452 f) ∉ (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv) := by
  simpa only [nb068_alpha_dummy_452] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv) 1

theorem nb068_distinct_378 (f : Var) : (nb068_alpha_dummy_451 f) ≠ (nb068_alpha_dummy_452 f) := by
  simpa only [nb068_alpha_dummy_451, nb068_alpha_dummy_452] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_410 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_409 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_379 : (nb068_alpha_dummy_421) ∉ (((Class.cv (nb068_alpha_dummy_414))).fv) := by
  simpa only [nb068_alpha_dummy_421] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_414))).fv) 0

theorem nb068_fresh_380 : (nb068_alpha_dummy_422) ∉ (((Class.cv (nb068_alpha_dummy_414))).fv) := by
  simpa only [nb068_alpha_dummy_422] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_414))).fv) 1

theorem nb068_distinct_381 : (nb068_alpha_dummy_421) ≠ (nb068_alpha_dummy_422) := by
  simpa only [nb068_alpha_dummy_421, nb068_alpha_dummy_422] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_414))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_382 (f : Var) : (nb068_alpha_dummy_423 f) ∉ (((Class.cv (nb068_alpha_dummy_416 f))).fv) := by
  simpa only [nb068_alpha_dummy_423] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_416 f))).fv) 0

theorem nb068_fresh_383 (f : Var) : (nb068_alpha_dummy_424 f) ∉ (((Class.cv (nb068_alpha_dummy_416 f))).fv) := by
  simpa only [nb068_alpha_dummy_424] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_416 f))).fv) 1

theorem nb068_distinct_384 (f : Var) : (nb068_alpha_dummy_423 f) ≠ (nb068_alpha_dummy_424 f) := by
  simpa only [nb068_alpha_dummy_423, nb068_alpha_dummy_424] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_416 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_385 : (nb068_alpha_dummy_427) ∉ (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_427] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_386 : (nb068_alpha_dummy_428) ∉ (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_428] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_387 : (nb068_alpha_dummy_429) ∉ (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_429] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_388 : (nb068_alpha_dummy_427) ≠ (nb068_alpha_dummy_428) := by
  simpa only [nb068_alpha_dummy_427, nb068_alpha_dummy_428] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_389 : (nb068_alpha_dummy_427) ≠ (nb068_alpha_dummy_429) := by
  simpa only [nb068_alpha_dummy_427, nb068_alpha_dummy_429] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_390 : (nb068_alpha_dummy_428) ≠ (nb068_alpha_dummy_429) := by
  simpa only [nb068_alpha_dummy_428, nb068_alpha_dummy_429] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_391 (f : Var) : (nb068_alpha_dummy_430 f) ∉ (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_430] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_392 (f : Var) : (nb068_alpha_dummy_431 f) ∉ (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_431] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_393 (f : Var) : (nb068_alpha_dummy_432 f) ∉ (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_432] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_394 (f : Var) : (nb068_alpha_dummy_430 f) ≠ (nb068_alpha_dummy_431 f) := by
  simpa only [nb068_alpha_dummy_430, nb068_alpha_dummy_431] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_395 (f : Var) : (nb068_alpha_dummy_430 f) ≠ (nb068_alpha_dummy_432 f) := by
  simpa only [nb068_alpha_dummy_430, nb068_alpha_dummy_432] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_396 (f : Var) : (nb068_alpha_dummy_431 f) ≠ (nb068_alpha_dummy_432 f) := by
  simpa only [nb068_alpha_dummy_431, nb068_alpha_dummy_432] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_397 : (nb068_alpha_dummy_439) ∉ (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_428))).fv) := by
  simpa only [nb068_alpha_dummy_439] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_428))).fv) 0

theorem nb068_fresh_398 : (nb068_alpha_dummy_435) ∉ (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) := by
  simpa only [nb068_alpha_dummy_435] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_428))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) 0

theorem nb068_fresh_399 : (nb068_alpha_dummy_441) ∉ (((Class.cv (nb068_alpha_dummy_429))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) := by
  simpa only [nb068_alpha_dummy_441] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_429))).fv ∪ ((Class.cv (nb068_alpha_dummy_429))).fv) 0

theorem nb068_fresh_400 (f : Var) : (nb068_alpha_dummy_440 f) ∉ (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_431 f))).fv) := by
  simpa only [nb068_alpha_dummy_440] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_431 f))).fv) 0

theorem nb068_fresh_401 (f : Var) : (nb068_alpha_dummy_436 f) ∉ (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) := by
  simpa only [nb068_alpha_dummy_436] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_431 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) 0

theorem nb068_fresh_402 (f : Var) : (nb068_alpha_dummy_442 f) ∉ (((Class.cv (nb068_alpha_dummy_432 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) := by
  simpa only [nb068_alpha_dummy_442] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_432 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_432 f))).fv) 0

theorem nb068_fresh_403 : (nb068_alpha_dummy_457) ∉ (((Class.cv (nb068_alpha_dummy_450))).fv) := by
  simpa only [nb068_alpha_dummy_457] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_450))).fv) 0

theorem nb068_fresh_404 : (nb068_alpha_dummy_458) ∉ (((Class.cv (nb068_alpha_dummy_450))).fv) := by
  simpa only [nb068_alpha_dummy_458] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_450))).fv) 1

theorem nb068_distinct_405 : (nb068_alpha_dummy_457) ≠ (nb068_alpha_dummy_458) := by
  simpa only [nb068_alpha_dummy_457, nb068_alpha_dummy_458] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_450))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_406 (f : Var) : (nb068_alpha_dummy_459 f) ∉ (((Class.cv (nb068_alpha_dummy_452 f))).fv) := by
  simpa only [nb068_alpha_dummy_459] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_452 f))).fv) 0

theorem nb068_fresh_407 (f : Var) : (nb068_alpha_dummy_460 f) ∉ (((Class.cv (nb068_alpha_dummy_452 f))).fv) := by
  simpa only [nb068_alpha_dummy_460] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_452 f))).fv) 1

theorem nb068_distinct_408 (f : Var) : (nb068_alpha_dummy_459 f) ≠ (nb068_alpha_dummy_460 f) := by
  simpa only [nb068_alpha_dummy_459, nb068_alpha_dummy_460] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_452 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_409 : (nb068_alpha_dummy_463) ∉ (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_463] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_410 : (nb068_alpha_dummy_464) ∉ (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_464] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_411 : (nb068_alpha_dummy_465) ∉ (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_465] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_412 : (nb068_alpha_dummy_463) ≠ (nb068_alpha_dummy_464) := by
  simpa only [nb068_alpha_dummy_463, nb068_alpha_dummy_464] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_413 : (nb068_alpha_dummy_463) ≠ (nb068_alpha_dummy_465) := by
  simpa only [nb068_alpha_dummy_463, nb068_alpha_dummy_465] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_414 : (nb068_alpha_dummy_464) ≠ (nb068_alpha_dummy_465) := by
  simpa only [nb068_alpha_dummy_464, nb068_alpha_dummy_465] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_457))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_415 (f : Var) : (nb068_alpha_dummy_466 f) ∉ (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_466] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_416 (f : Var) : (nb068_alpha_dummy_467 f) ∉ (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_467] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_417 (f : Var) : (nb068_alpha_dummy_468 f) ∉ (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_468] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_418 (f : Var) : (nb068_alpha_dummy_466 f) ≠ (nb068_alpha_dummy_467 f) := by
  simpa only [nb068_alpha_dummy_466, nb068_alpha_dummy_467] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_419 (f : Var) : (nb068_alpha_dummy_466 f) ≠ (nb068_alpha_dummy_468 f) := by
  simpa only [nb068_alpha_dummy_466, nb068_alpha_dummy_468] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_420 (f : Var) : (nb068_alpha_dummy_467 f) ≠ (nb068_alpha_dummy_468 f) := by
  simpa only [nb068_alpha_dummy_467, nb068_alpha_dummy_468] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_459 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_421 : (nb068_alpha_dummy_475) ∉ (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_464))).fv) := by
  simpa only [nb068_alpha_dummy_475] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_464))).fv) 0

theorem nb068_fresh_422 : (nb068_alpha_dummy_471) ∉ (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) := by
  simpa only [nb068_alpha_dummy_471] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_464))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) 0

theorem nb068_fresh_423 : (nb068_alpha_dummy_477) ∉ (((Class.cv (nb068_alpha_dummy_465))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) := by
  simpa only [nb068_alpha_dummy_477] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_465))).fv ∪ ((Class.cv (nb068_alpha_dummy_465))).fv) 0

theorem nb068_fresh_424 (f : Var) : (nb068_alpha_dummy_476 f) ∉ (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_467 f))).fv) := by
  simpa only [nb068_alpha_dummy_476] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_467 f))).fv) 0

theorem nb068_fresh_425 (f : Var) : (nb068_alpha_dummy_472 f) ∉ (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv) := by
  simpa only [nb068_alpha_dummy_472] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_467 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv) 0

theorem nb068_fresh_426 (f : Var) : (nb068_alpha_dummy_478 f) ∉ (((Class.cv (nb068_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv) := by
  simpa only [nb068_alpha_dummy_478] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_468 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_468 f))).fv) 0

theorem nb068_fresh_427 : (nb068_alpha_dummy_493) ∉ (((Class.cv (nb068_alpha_dummy_486))).fv) := by
  simpa only [nb068_alpha_dummy_493] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_486))).fv) 0

theorem nb068_fresh_428 : (nb068_alpha_dummy_494) ∉ (((Class.cv (nb068_alpha_dummy_486))).fv) := by
  simpa only [nb068_alpha_dummy_494] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_486))).fv) 1

theorem nb068_distinct_429 : (nb068_alpha_dummy_493) ≠ (nb068_alpha_dummy_494) := by
  simpa only [nb068_alpha_dummy_493, nb068_alpha_dummy_494] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_486))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_430 (f : Var) : (nb068_alpha_dummy_495 f) ∉ (((Class.cv (nb068_alpha_dummy_488 f))).fv) := by
  simpa only [nb068_alpha_dummy_495] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_488 f))).fv) 0

theorem nb068_fresh_431 (f : Var) : (nb068_alpha_dummy_496 f) ∉ (((Class.cv (nb068_alpha_dummy_488 f))).fv) := by
  simpa only [nb068_alpha_dummy_496] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_488 f))).fv) 1

theorem nb068_distinct_432 (f : Var) : (nb068_alpha_dummy_495 f) ≠ (nb068_alpha_dummy_496 f) := by
  simpa only [nb068_alpha_dummy_495, nb068_alpha_dummy_496] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_488 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_433 : (nb068_alpha_dummy_499) ∉ (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_499] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_434 : (nb068_alpha_dummy_500) ∉ (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_500] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_435 : (nb068_alpha_dummy_501) ∉ (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_501] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_436 : (nb068_alpha_dummy_499) ≠ (nb068_alpha_dummy_500) := by
  simpa only [nb068_alpha_dummy_499, nb068_alpha_dummy_500] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_437 : (nb068_alpha_dummy_499) ≠ (nb068_alpha_dummy_501) := by
  simpa only [nb068_alpha_dummy_499, nb068_alpha_dummy_501] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_438 : (nb068_alpha_dummy_500) ≠ (nb068_alpha_dummy_501) := by
  simpa only [nb068_alpha_dummy_500, nb068_alpha_dummy_501] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_439 (f : Var) : (nb068_alpha_dummy_502 f) ∉ (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_502] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_440 (f : Var) : (nb068_alpha_dummy_503 f) ∉ (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_503] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_441 (f : Var) : (nb068_alpha_dummy_504 f) ∉ (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_504] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_442 (f : Var) : (nb068_alpha_dummy_502 f) ≠ (nb068_alpha_dummy_503 f) := by
  simpa only [nb068_alpha_dummy_502, nb068_alpha_dummy_503] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_443 (f : Var) : (nb068_alpha_dummy_502 f) ≠ (nb068_alpha_dummy_504 f) := by
  simpa only [nb068_alpha_dummy_502, nb068_alpha_dummy_504] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_444 (f : Var) : (nb068_alpha_dummy_503 f) ≠ (nb068_alpha_dummy_504 f) := by
  simpa only [nb068_alpha_dummy_503, nb068_alpha_dummy_504] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_445 : (nb068_alpha_dummy_511) ∉ (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_500))).fv) := by
  simpa only [nb068_alpha_dummy_511] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_500))).fv) 0

theorem nb068_fresh_446 : (nb068_alpha_dummy_507) ∉ (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) := by
  simpa only [nb068_alpha_dummy_507] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) 0

theorem nb068_fresh_447 : (nb068_alpha_dummy_513) ∉ (((Class.cv (nb068_alpha_dummy_501))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) := by
  simpa only [nb068_alpha_dummy_513] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_501))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) 0

theorem nb068_fresh_448 (f : Var) : (nb068_alpha_dummy_512 f) ∉ (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_503 f))).fv) := by
  simpa only [nb068_alpha_dummy_512] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_503 f))).fv) 0

theorem nb068_fresh_449 (f : Var) : (nb068_alpha_dummy_508 f) ∉ (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) := by
  simpa only [nb068_alpha_dummy_508] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) 0

theorem nb068_fresh_450 (f : Var) : (nb068_alpha_dummy_514 f) ∉ (((Class.cv (nb068_alpha_dummy_504 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) := by
  simpa only [nb068_alpha_dummy_514] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_504 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) 0

theorem nb068_fresh_451 (f : Var) : (nb068_alpha_dummy_127 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb068_alpha_dummy_127] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb068_fresh_452 (f : Var) : (nb068_alpha_dummy_128 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb068_alpha_dummy_128] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb068_distinct_453 (f : Var) : (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_128 f) := by
  simpa only [nb068_alpha_dummy_127, nb068_alpha_dummy_128] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_454 (f : Var) : (nb068_alpha_dummy_048 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb068_alpha_dummy_048] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb068_fresh_455 (f : Var) : (nb068_alpha_dummy_049 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb068_alpha_dummy_049] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb068_fresh_456 (f : Var) : (nb068_alpha_dummy_050 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb068_alpha_dummy_050] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb068_distinct_457 (f : Var) : (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_049 f) := by
  simpa only [nb068_alpha_dummy_048, nb068_alpha_dummy_049] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_458 (f : Var) : (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_050 f) := by
  simpa only [nb068_alpha_dummy_048, nb068_alpha_dummy_050] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_459 (f : Var) : (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_050 f) := by
  simpa only [nb068_alpha_dummy_049, nb068_alpha_dummy_050] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_460 (f : Var) : (nb068_alpha_dummy_285 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_285] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0

theorem nb068_fresh_461 (f : Var) : (nb068_alpha_dummy_286 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_286] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1

theorem nb068_distinct_462 (f : Var) : (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_286 f) := by
  simpa only [nb068_alpha_dummy_285, nb068_alpha_dummy_286] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_463 (x : Var) (y : Var) : (nb068_alpha_dummy_007 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb068_alpha_dummy_007] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb068_fresh_464 (x : Var) (y : Var) : (nb068_alpha_dummy_008 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb068_alpha_dummy_008] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb068_distinct_465 (x : Var) (y : Var) : (nb068_alpha_dummy_007 x y) ≠ (nb068_alpha_dummy_008 x y) := by
  simpa only [nb068_alpha_dummy_007, nb068_alpha_dummy_008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_466 : (nb068_alpha_dummy_017) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_013))).fv) := by
  simpa only [nb068_alpha_dummy_017] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_013))).fv) 0

theorem nb068_fresh_467 (x : Var) (y : Var) : (nb068_alpha_dummy_018 x y) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_015 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_015 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_015 x y))).fv) := by
  simpa only [nb068_alpha_dummy_018] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_015 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_015 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_015 x y))).fv) 0

theorem nb068_fresh_468 : (nb068_alpha_dummy_065) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_061)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_061))).fv) := by
  simpa only [nb068_alpha_dummy_065] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_061)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_061))).fv) 0

theorem nb068_fresh_469 (f : Var) : (nb068_alpha_dummy_066 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_063 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_063 f))).fv) := by
  simpa only [nb068_alpha_dummy_066] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_063 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_063 f))).fv) 0

theorem nb068_fresh_470 : (nb068_alpha_dummy_101) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_097)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_097)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_097))).fv) := by
  simpa only [nb068_alpha_dummy_101] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_097)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_097)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_097))).fv) 0

theorem nb068_fresh_471 (f : Var) : (nb068_alpha_dummy_102 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_099 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_099 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_099 f))).fv) := by
  simpa only [nb068_alpha_dummy_102] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_099 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_099 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_099 f))).fv) 0

theorem nb068_fresh_472 : (nb068_alpha_dummy_143) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_139))).fv) := by
  simpa only [nb068_alpha_dummy_143] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_139))).fv) 0

theorem nb068_fresh_473 (f : Var) : (nb068_alpha_dummy_144 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_141 f))).fv) := by
  simpa only [nb068_alpha_dummy_144] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_141 f))).fv) 0

theorem nb068_fresh_474 : (nb068_alpha_dummy_179) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_175))).fv) := by
  simpa only [nb068_alpha_dummy_179] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_175))).fv) 0

theorem nb068_fresh_475 (f : Var) : (nb068_alpha_dummy_180 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_177 f))).fv) := by
  simpa only [nb068_alpha_dummy_180] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_177 f))).fv) 0

theorem nb068_fresh_476 : (nb068_alpha_dummy_215) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_211)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_211)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_211))).fv) := by
  simpa only [nb068_alpha_dummy_215] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_211)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_211)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_211))).fv) 0

theorem nb068_fresh_477 (f : Var) : (nb068_alpha_dummy_216 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_213 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_213 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_213 f))).fv) := by
  simpa only [nb068_alpha_dummy_216] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_213 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_213 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_213 f))).fv) 0

theorem nb068_fresh_478 : (nb068_alpha_dummy_255) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_251)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_251)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_251))).fv) := by
  simpa only [nb068_alpha_dummy_255] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_251)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_251)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_251))).fv) 0

theorem nb068_fresh_479 (f : Var) : (nb068_alpha_dummy_256 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_253 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_253 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_253 f))).fv) := by
  simpa only [nb068_alpha_dummy_256] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_253 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_253 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_253 f))).fv) 0

theorem nb068_fresh_480 : (nb068_alpha_dummy_299) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_295))).fv) := by
  simpa only [nb068_alpha_dummy_299] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_295))).fv) 0

theorem nb068_fresh_481 (f : Var) : (nb068_alpha_dummy_300 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_297 f))).fv) := by
  simpa only [nb068_alpha_dummy_300] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_297 f))).fv) 0

theorem nb068_fresh_482 : (nb068_alpha_dummy_347) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_343)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_343))).fv) := by
  simpa only [nb068_alpha_dummy_347] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_343)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_343))).fv) 0

theorem nb068_fresh_483 (f : Var) : (nb068_alpha_dummy_348 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_345 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_345 f))).fv) := by
  simpa only [nb068_alpha_dummy_348] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_345 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_345 f))).fv) 0

theorem nb068_fresh_484 : (nb068_alpha_dummy_383) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_379)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_379))).fv) := by
  simpa only [nb068_alpha_dummy_383] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_379)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_379))).fv) 0

theorem nb068_fresh_485 (f : Var) : (nb068_alpha_dummy_384 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_381 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_381 f))).fv) := by
  simpa only [nb068_alpha_dummy_384] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_381 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_381 f))).fv) 0

theorem nb068_fresh_486 : (nb068_alpha_dummy_425) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_421))).fv) := by
  simpa only [nb068_alpha_dummy_425] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_421))).fv) 0

theorem nb068_fresh_487 (f : Var) : (nb068_alpha_dummy_426 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_423 f))).fv) := by
  simpa only [nb068_alpha_dummy_426] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_423 f))).fv) 0

theorem nb068_fresh_488 : (nb068_alpha_dummy_461) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_457)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_457)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_457))).fv) := by
  simpa only [nb068_alpha_dummy_461] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_457)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_457)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_457))).fv) 0

theorem nb068_fresh_489 (f : Var) : (nb068_alpha_dummy_462 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_459 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_459 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_459 f))).fv) := by
  simpa only [nb068_alpha_dummy_462] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_459 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_459 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_459 f))).fv) 0

theorem nb068_fresh_490 : (nb068_alpha_dummy_497) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_493)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_493)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_493))).fv) := by
  simpa only [nb068_alpha_dummy_497] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_493)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_493)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_493))).fv) 0

theorem nb068_fresh_491 (f : Var) : (nb068_alpha_dummy_498 f) ∉ (((Wff.classMem (Class.cv (nb068_alpha_dummy_495 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_495 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_495 f))).fv) := by
  simpa only [nb068_alpha_dummy_498] using freshVar_not_mem (((Wff.classMem (Class.cv (nb068_alpha_dummy_495 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_495 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_495 f))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
