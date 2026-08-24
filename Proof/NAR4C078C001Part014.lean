import NAR4C078C001Part013

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

theorem nb078_fresh_554 : (nb078_alpha_dummy_332) ∉ (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) := by
  simpa only [nb078_alpha_dummy_332] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) 1

theorem nb078_distinct_555 : (nb078_alpha_dummy_331) ≠ (nb078_alpha_dummy_332) := by
  simpa only [nb078_alpha_dummy_331, nb078_alpha_dummy_332] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_556 : (nb078_alpha_dummy_445) ∉ (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) := by
  simpa only [nb078_alpha_dummy_445] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 0

theorem nb078_fresh_557 : (nb078_alpha_dummy_446) ∉ (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) := by
  simpa only [nb078_alpha_dummy_446] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 1

theorem nb078_distinct_558 : (nb078_alpha_dummy_445) ≠ (nb078_alpha_dummy_446) := by
  simpa only [nb078_alpha_dummy_445, nb078_alpha_dummy_446] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_559 (g : Var) : (nb078_alpha_dummy_297 g) ∉ (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) := by
  simpa only [nb078_alpha_dummy_297] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) 0

theorem nb078_fresh_560 (g : Var) : (nb078_alpha_dummy_298 g) ∉ (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) := by
  simpa only [nb078_alpha_dummy_298] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) 1

theorem nb078_distinct_561 (g : Var) : (nb078_alpha_dummy_297 g) ≠ (nb078_alpha_dummy_298 g) := by
  simpa only [nb078_alpha_dummy_297, nb078_alpha_dummy_298] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_562 (g : Var) : (nb078_alpha_dummy_333 g) ∉ (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) := by
  simpa only [nb078_alpha_dummy_333] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) 0

theorem nb078_fresh_563 (g : Var) : (nb078_alpha_dummy_334 g) ∉ (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) := by
  simpa only [nb078_alpha_dummy_334] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) 1

theorem nb078_distinct_564 (g : Var) : (nb078_alpha_dummy_333 g) ≠ (nb078_alpha_dummy_334 g) := by
  simpa only [nb078_alpha_dummy_333, nb078_alpha_dummy_334] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_565 (g : Var) : (nb078_alpha_dummy_447 g) ∉ (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) := by
  simpa only [nb078_alpha_dummy_447] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) 0

theorem nb078_fresh_566 (g : Var) : (nb078_alpha_dummy_448 g) ∉ (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) := by
  simpa only [nb078_alpha_dummy_448] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) 1

theorem nb078_distinct_567 (g : Var) : (nb078_alpha_dummy_447 g) ≠ (nb078_alpha_dummy_448 g) := by
  simpa only [nb078_alpha_dummy_447, nb078_alpha_dummy_448] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_568 : (nb078_alpha_dummy_303) ∉ (((Class.cv (nb078_alpha_dummy_296))).fv) := by
  simpa only [nb078_alpha_dummy_303] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_296))).fv) 0

theorem nb078_fresh_569 : (nb078_alpha_dummy_304) ∉ (((Class.cv (nb078_alpha_dummy_296))).fv) := by
  simpa only [nb078_alpha_dummy_304] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_296))).fv) 1

theorem nb078_distinct_570 : (nb078_alpha_dummy_303) ≠ (nb078_alpha_dummy_304) := by
  simpa only [nb078_alpha_dummy_303, nb078_alpha_dummy_304] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_296))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_571 (g : Var) : (nb078_alpha_dummy_305 g) ∉ (((Class.cv (nb078_alpha_dummy_298 g))).fv) := by
  simpa only [nb078_alpha_dummy_305] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_298 g))).fv) 0

theorem nb078_fresh_572 (g : Var) : (nb078_alpha_dummy_306 g) ∉ (((Class.cv (nb078_alpha_dummy_298 g))).fv) := by
  simpa only [nb078_alpha_dummy_306] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_298 g))).fv) 1

theorem nb078_distinct_573 (g : Var) : (nb078_alpha_dummy_305 g) ≠ (nb078_alpha_dummy_306 g) := by
  simpa only [nb078_alpha_dummy_305, nb078_alpha_dummy_306] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_298 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_574 : (nb078_alpha_dummy_309) ∉ (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_309] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_575 : (nb078_alpha_dummy_310) ∉ (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_310] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_576 : (nb078_alpha_dummy_311) ∉ (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_311] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_577 : (nb078_alpha_dummy_309) ≠ (nb078_alpha_dummy_310) := by
  simpa only [nb078_alpha_dummy_309, nb078_alpha_dummy_310] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_578 : (nb078_alpha_dummy_309) ≠ (nb078_alpha_dummy_311) := by
  simpa only [nb078_alpha_dummy_309, nb078_alpha_dummy_311] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_579 : (nb078_alpha_dummy_310) ≠ (nb078_alpha_dummy_311) := by
  simpa only [nb078_alpha_dummy_310, nb078_alpha_dummy_311] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_580 (g : Var) : (nb078_alpha_dummy_312 g) ∉ (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_312] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_581 (g : Var) : (nb078_alpha_dummy_313 g) ∉ (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_313] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_582 (g : Var) : (nb078_alpha_dummy_314 g) ∉ (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_314] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_583 (g : Var) : (nb078_alpha_dummy_312 g) ≠ (nb078_alpha_dummy_313 g) := by
  simpa only [nb078_alpha_dummy_312, nb078_alpha_dummy_313] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_584 (g : Var) : (nb078_alpha_dummy_312 g) ≠ (nb078_alpha_dummy_314 g) := by
  simpa only [nb078_alpha_dummy_312, nb078_alpha_dummy_314] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_585 (g : Var) : (nb078_alpha_dummy_313 g) ≠ (nb078_alpha_dummy_314 g) := by
  simpa only [nb078_alpha_dummy_313, nb078_alpha_dummy_314] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_586 : (nb078_alpha_dummy_321) ∉ (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_310))).fv) := by
  simpa only [nb078_alpha_dummy_321] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_310))).fv) 0

theorem nb078_fresh_587 : (nb078_alpha_dummy_317) ∉ (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) := by
  simpa only [nb078_alpha_dummy_317] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) 0

theorem nb078_fresh_588 : (nb078_alpha_dummy_323) ∉ (((Class.cv (nb078_alpha_dummy_311))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) := by
  simpa only [nb078_alpha_dummy_323] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_311))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) 0

theorem nb078_fresh_589 (g : Var) : (nb078_alpha_dummy_322 g) ∉ (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_313 g))).fv) := by
  simpa only [nb078_alpha_dummy_322] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_313 g))).fv) 0

theorem nb078_fresh_590 (g : Var) : (nb078_alpha_dummy_318 g) ∉ (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) := by
  simpa only [nb078_alpha_dummy_318] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) 0

theorem nb078_fresh_591 (g : Var) : (nb078_alpha_dummy_324 g) ∉ (((Class.cv (nb078_alpha_dummy_314 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) := by
  simpa only [nb078_alpha_dummy_324] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_314 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) 0

theorem nb078_fresh_592 : (nb078_alpha_dummy_339) ∉ (((Class.cv (nb078_alpha_dummy_332))).fv) := by
  simpa only [nb078_alpha_dummy_339] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_332))).fv) 0

theorem nb078_fresh_593 : (nb078_alpha_dummy_340) ∉ (((Class.cv (nb078_alpha_dummy_332))).fv) := by
  simpa only [nb078_alpha_dummy_340] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_332))).fv) 1

theorem nb078_distinct_594 : (nb078_alpha_dummy_339) ≠ (nb078_alpha_dummy_340) := by
  simpa only [nb078_alpha_dummy_339, nb078_alpha_dummy_340] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_332))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_595 (g : Var) : (nb078_alpha_dummy_341 g) ∉ (((Class.cv (nb078_alpha_dummy_334 g))).fv) := by
  simpa only [nb078_alpha_dummy_341] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_334 g))).fv) 0

theorem nb078_fresh_596 (g : Var) : (nb078_alpha_dummy_342 g) ∉ (((Class.cv (nb078_alpha_dummy_334 g))).fv) := by
  simpa only [nb078_alpha_dummy_342] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_334 g))).fv) 1

theorem nb078_distinct_597 (g : Var) : (nb078_alpha_dummy_341 g) ≠ (nb078_alpha_dummy_342 g) := by
  simpa only [nb078_alpha_dummy_341, nb078_alpha_dummy_342] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_334 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_598 : (nb078_alpha_dummy_345) ∉ (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_345] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_599 : (nb078_alpha_dummy_346) ∉ (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_346] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_600 : (nb078_alpha_dummy_347) ∉ (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_347] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_601 : (nb078_alpha_dummy_345) ≠ (nb078_alpha_dummy_346) := by
  simpa only [nb078_alpha_dummy_345, nb078_alpha_dummy_346] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_602 : (nb078_alpha_dummy_345) ≠ (nb078_alpha_dummy_347) := by
  simpa only [nb078_alpha_dummy_345, nb078_alpha_dummy_347] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_603 : (nb078_alpha_dummy_346) ≠ (nb078_alpha_dummy_347) := by
  simpa only [nb078_alpha_dummy_346, nb078_alpha_dummy_347] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_604 (g : Var) : (nb078_alpha_dummy_348 g) ∉ (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_348] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_605 (g : Var) : (nb078_alpha_dummy_349 g) ∉ (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_349] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_606 (g : Var) : (nb078_alpha_dummy_350 g) ∉ (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_350] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_607 (g : Var) : (nb078_alpha_dummy_348 g) ≠ (nb078_alpha_dummy_349 g) := by
  simpa only [nb078_alpha_dummy_348, nb078_alpha_dummy_349] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_608 (g : Var) : (nb078_alpha_dummy_348 g) ≠ (nb078_alpha_dummy_350 g) := by
  simpa only [nb078_alpha_dummy_348, nb078_alpha_dummy_350] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_609 (g : Var) : (nb078_alpha_dummy_349 g) ≠ (nb078_alpha_dummy_350 g) := by
  simpa only [nb078_alpha_dummy_349, nb078_alpha_dummy_350] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_610 : (nb078_alpha_dummy_357) ∉ (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_346))).fv) := by
  simpa only [nb078_alpha_dummy_357] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_346))).fv) 0

theorem nb078_fresh_611 : (nb078_alpha_dummy_353) ∉ (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) := by
  simpa only [nb078_alpha_dummy_353] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_346))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) 0

theorem nb078_fresh_612 : (nb078_alpha_dummy_359) ∉ (((Class.cv (nb078_alpha_dummy_347))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) := by
  simpa only [nb078_alpha_dummy_359] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_347))).fv ∪ ((Class.cv (nb078_alpha_dummy_347))).fv) 0

theorem nb078_fresh_613 (g : Var) : (nb078_alpha_dummy_358 g) ∉ (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_349 g))).fv) := by
  simpa only [nb078_alpha_dummy_358] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_349 g))).fv) 0

theorem nb078_fresh_614 (g : Var) : (nb078_alpha_dummy_354 g) ∉ (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) := by
  simpa only [nb078_alpha_dummy_354] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_349 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) 0

theorem nb078_fresh_615 (g : Var) : (nb078_alpha_dummy_360 g) ∉ (((Class.cv (nb078_alpha_dummy_350 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) := by
  simpa only [nb078_alpha_dummy_360] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_350 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_350 g))).fv) 0

theorem nb078_fresh_616 : (nb078_alpha_dummy_373) ∉ (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) := by
  simpa only [nb078_alpha_dummy_373] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) 0

theorem nb078_fresh_617 : (nb078_alpha_dummy_374) ∉ (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) := by
  simpa only [nb078_alpha_dummy_374] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) 1

theorem nb078_distinct_618 : (nb078_alpha_dummy_373) ≠ (nb078_alpha_dummy_374) := by
  simpa only [nb078_alpha_dummy_373, nb078_alpha_dummy_374] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_367))).fv ∪ ((Class.cv (nb078_alpha_dummy_368))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_619 : (nb078_alpha_dummy_409) ∉ (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) := by
  simpa only [nb078_alpha_dummy_409] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) 0

theorem nb078_fresh_620 : (nb078_alpha_dummy_410) ∉ (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) := by
  simpa only [nb078_alpha_dummy_410] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) 1

theorem nb078_distinct_621 : (nb078_alpha_dummy_409) ≠ (nb078_alpha_dummy_410) := by
  simpa only [nb078_alpha_dummy_409, nb078_alpha_dummy_410] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_368))).fv ∪ ((Class.cv (nb078_alpha_dummy_367))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_622 (g : Var) : (nb078_alpha_dummy_375 g) ∉ (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) := by
  simpa only [nb078_alpha_dummy_375] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) 0

theorem nb078_fresh_623 (g : Var) : (nb078_alpha_dummy_376 g) ∉ (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) := by
  simpa only [nb078_alpha_dummy_376] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) 1

theorem nb078_distinct_624 (g : Var) : (nb078_alpha_dummy_375 g) ≠ (nb078_alpha_dummy_376 g) := by
  simpa only [nb078_alpha_dummy_375, nb078_alpha_dummy_376] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_625 (g : Var) : (nb078_alpha_dummy_411 g) ∉ (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) := by
  simpa only [nb078_alpha_dummy_411] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) 0

theorem nb078_fresh_626 (g : Var) : (nb078_alpha_dummy_412 g) ∉ (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) := by
  simpa only [nb078_alpha_dummy_412] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) 1

theorem nb078_distinct_627 (g : Var) : (nb078_alpha_dummy_411 g) ≠ (nb078_alpha_dummy_412 g) := by
  simpa only [nb078_alpha_dummy_411, nb078_alpha_dummy_412] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_628 : (nb078_alpha_dummy_381) ∉ (((Class.cv (nb078_alpha_dummy_374))).fv) := by
  simpa only [nb078_alpha_dummy_381] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_374))).fv) 0

theorem nb078_fresh_629 : (nb078_alpha_dummy_382) ∉ (((Class.cv (nb078_alpha_dummy_374))).fv) := by
  simpa only [nb078_alpha_dummy_382] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_374))).fv) 1

theorem nb078_distinct_630 : (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_382) := by
  simpa only [nb078_alpha_dummy_381, nb078_alpha_dummy_382] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_631 (g : Var) : (nb078_alpha_dummy_383 g) ∉ (((Class.cv (nb078_alpha_dummy_376 g))).fv) := by
  simpa only [nb078_alpha_dummy_383] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_376 g))).fv) 0

theorem nb078_fresh_632 (g : Var) : (nb078_alpha_dummy_384 g) ∉ (((Class.cv (nb078_alpha_dummy_376 g))).fv) := by
  simpa only [nb078_alpha_dummy_384] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_376 g))).fv) 1

theorem nb078_distinct_633 (g : Var) : (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_384 g) := by
  simpa only [nb078_alpha_dummy_383, nb078_alpha_dummy_384] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_376 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_634 : (nb078_alpha_dummy_387) ∉ (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_387] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_635 : (nb078_alpha_dummy_388) ∉ (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_388] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_636 : (nb078_alpha_dummy_389) ∉ (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_389] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_637 : (nb078_alpha_dummy_387) ≠ (nb078_alpha_dummy_388) := by
  simpa only [nb078_alpha_dummy_387, nb078_alpha_dummy_388] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_638 : (nb078_alpha_dummy_387) ≠ (nb078_alpha_dummy_389) := by
  simpa only [nb078_alpha_dummy_387, nb078_alpha_dummy_389] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_639 : (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_389) := by
  simpa only [nb078_alpha_dummy_388, nb078_alpha_dummy_389] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_640 (g : Var) : (nb078_alpha_dummy_390 g) ∉ (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_390] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_641 (g : Var) : (nb078_alpha_dummy_391 g) ∉ (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_391] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_642 (g : Var) : (nb078_alpha_dummy_392 g) ∉ (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_392] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_643 (g : Var) : (nb078_alpha_dummy_390 g) ≠ (nb078_alpha_dummy_391 g) := by
  simpa only [nb078_alpha_dummy_390, nb078_alpha_dummy_391] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_644 (g : Var) : (nb078_alpha_dummy_390 g) ≠ (nb078_alpha_dummy_392 g) := by
  simpa only [nb078_alpha_dummy_390, nb078_alpha_dummy_392] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_645 (g : Var) : (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_392 g) := by
  simpa only [nb078_alpha_dummy_391, nb078_alpha_dummy_392] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_646 : (nb078_alpha_dummy_399) ∉ (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_388))).fv) := by
  simpa only [nb078_alpha_dummy_399] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_388))).fv) 0

theorem nb078_fresh_647 : (nb078_alpha_dummy_395) ∉ (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) := by
  simpa only [nb078_alpha_dummy_395] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_388))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) 0

theorem nb078_fresh_648 : (nb078_alpha_dummy_401) ∉ (((Class.cv (nb078_alpha_dummy_389))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) := by
  simpa only [nb078_alpha_dummy_401] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_389))).fv ∪ ((Class.cv (nb078_alpha_dummy_389))).fv) 0

theorem nb078_fresh_649 (g : Var) : (nb078_alpha_dummy_400 g) ∉ (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_391 g))).fv) := by
  simpa only [nb078_alpha_dummy_400] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_391 g))).fv) 0

theorem nb078_fresh_650 (g : Var) : (nb078_alpha_dummy_396 g) ∉ (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) := by
  simpa only [nb078_alpha_dummy_396] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_391 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) 0

theorem nb078_fresh_651 (g : Var) : (nb078_alpha_dummy_402 g) ∉ (((Class.cv (nb078_alpha_dummy_392 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) := by
  simpa only [nb078_alpha_dummy_402] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_392 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_392 g))).fv) 0

theorem nb078_fresh_652 : (nb078_alpha_dummy_417) ∉ (((Class.cv (nb078_alpha_dummy_410))).fv) := by
  simpa only [nb078_alpha_dummy_417] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_410))).fv) 0

theorem nb078_fresh_653 : (nb078_alpha_dummy_418) ∉ (((Class.cv (nb078_alpha_dummy_410))).fv) := by
  simpa only [nb078_alpha_dummy_418] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_410))).fv) 1

theorem nb078_distinct_654 : (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_418) := by
  simpa only [nb078_alpha_dummy_417, nb078_alpha_dummy_418] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_410))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_655 (g : Var) : (nb078_alpha_dummy_419 g) ∉ (((Class.cv (nb078_alpha_dummy_412 g))).fv) := by
  simpa only [nb078_alpha_dummy_419] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_412 g))).fv) 0

theorem nb078_fresh_656 (g : Var) : (nb078_alpha_dummy_420 g) ∉ (((Class.cv (nb078_alpha_dummy_412 g))).fv) := by
  simpa only [nb078_alpha_dummy_420] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_412 g))).fv) 1

theorem nb078_distinct_657 (g : Var) : (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_420 g) := by
  simpa only [nb078_alpha_dummy_419, nb078_alpha_dummy_420] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_412 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_658 : (nb078_alpha_dummy_423) ∉ (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_423] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_659 : (nb078_alpha_dummy_424) ∉ (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_424] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_660 : (nb078_alpha_dummy_425) ∉ (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_425] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_661 : (nb078_alpha_dummy_423) ≠ (nb078_alpha_dummy_424) := by
  simpa only [nb078_alpha_dummy_423, nb078_alpha_dummy_424] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_662 : (nb078_alpha_dummy_423) ≠ (nb078_alpha_dummy_425) := by
  simpa only [nb078_alpha_dummy_423, nb078_alpha_dummy_425] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_663 : (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_425) := by
  simpa only [nb078_alpha_dummy_424, nb078_alpha_dummy_425] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_664 (g : Var) : (nb078_alpha_dummy_426 g) ∉ (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_426] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_665 (g : Var) : (nb078_alpha_dummy_427 g) ∉ (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_427] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_666 (g : Var) : (nb078_alpha_dummy_428 g) ∉ (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_428] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_667 (g : Var) : (nb078_alpha_dummy_426 g) ≠ (nb078_alpha_dummy_427 g) := by
  simpa only [nb078_alpha_dummy_426, nb078_alpha_dummy_427] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_668 (g : Var) : (nb078_alpha_dummy_426 g) ≠ (nb078_alpha_dummy_428 g) := by
  simpa only [nb078_alpha_dummy_426, nb078_alpha_dummy_428] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_669 (g : Var) : (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_428 g) := by
  simpa only [nb078_alpha_dummy_427, nb078_alpha_dummy_428] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_670 : (nb078_alpha_dummy_435) ∉ (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_424))).fv) := by
  simpa only [nb078_alpha_dummy_435] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_424))).fv) 0

theorem nb078_fresh_671 : (nb078_alpha_dummy_431) ∉ (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) := by
  simpa only [nb078_alpha_dummy_431] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_424))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) 0

theorem nb078_fresh_672 : (nb078_alpha_dummy_437) ∉ (((Class.cv (nb078_alpha_dummy_425))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) := by
  simpa only [nb078_alpha_dummy_437] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_425))).fv ∪ ((Class.cv (nb078_alpha_dummy_425))).fv) 0

theorem nb078_fresh_673 (g : Var) : (nb078_alpha_dummy_436 g) ∉ (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_427 g))).fv) := by
  simpa only [nb078_alpha_dummy_436] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_427 g))).fv) 0

theorem nb078_fresh_674 (g : Var) : (nb078_alpha_dummy_432 g) ∉ (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) := by
  simpa only [nb078_alpha_dummy_432] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_427 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) 0

theorem nb078_fresh_675 (g : Var) : (nb078_alpha_dummy_438 g) ∉ (((Class.cv (nb078_alpha_dummy_428 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) := by
  simpa only [nb078_alpha_dummy_438] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_428 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_428 g))).fv) 0

theorem nb078_fresh_676 : (nb078_alpha_dummy_453) ∉ (((Class.cv (nb078_alpha_dummy_446))).fv) := by
  simpa only [nb078_alpha_dummy_453] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_446))).fv) 0

theorem nb078_fresh_677 : (nb078_alpha_dummy_454) ∉ (((Class.cv (nb078_alpha_dummy_446))).fv) := by
  simpa only [nb078_alpha_dummy_454] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_446))).fv) 1

theorem nb078_distinct_678 : (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_454) := by
  simpa only [nb078_alpha_dummy_453, nb078_alpha_dummy_454] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_446))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_679 (g : Var) : (nb078_alpha_dummy_455 g) ∉ (((Class.cv (nb078_alpha_dummy_448 g))).fv) := by
  simpa only [nb078_alpha_dummy_455] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_448 g))).fv) 0

theorem nb078_fresh_680 (g : Var) : (nb078_alpha_dummy_456 g) ∉ (((Class.cv (nb078_alpha_dummy_448 g))).fv) := by
  simpa only [nb078_alpha_dummy_456] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_448 g))).fv) 1

theorem nb078_distinct_681 (g : Var) : (nb078_alpha_dummy_455 g) ≠ (nb078_alpha_dummy_456 g) := by
  simpa only [nb078_alpha_dummy_455, nb078_alpha_dummy_456] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_448 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_682 : (nb078_alpha_dummy_459) ∉ (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_459] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_683 : (nb078_alpha_dummy_460) ∉ (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_460] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_684 : (nb078_alpha_dummy_461) ∉ (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_461] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_685 : (nb078_alpha_dummy_459) ≠ (nb078_alpha_dummy_460) := by
  simpa only [nb078_alpha_dummy_459, nb078_alpha_dummy_460] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_686 : (nb078_alpha_dummy_459) ≠ (nb078_alpha_dummy_461) := by
  simpa only [nb078_alpha_dummy_459, nb078_alpha_dummy_461] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_687 : (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_461) := by
  simpa only [nb078_alpha_dummy_460, nb078_alpha_dummy_461] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_688 (g : Var) : (nb078_alpha_dummy_462 g) ∉ (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_462] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_689 (g : Var) : (nb078_alpha_dummy_463 g) ∉ (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_463] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_690 (g : Var) : (nb078_alpha_dummy_464 g) ∉ (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_464] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_691 (g : Var) : (nb078_alpha_dummy_462 g) ≠ (nb078_alpha_dummy_463 g) := by
  simpa only [nb078_alpha_dummy_462, nb078_alpha_dummy_463] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_692 (g : Var) : (nb078_alpha_dummy_462 g) ≠ (nb078_alpha_dummy_464 g) := by
  simpa only [nb078_alpha_dummy_462, nb078_alpha_dummy_464] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_693 (g : Var) : (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_464 g) := by
  simpa only [nb078_alpha_dummy_463, nb078_alpha_dummy_464] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_694 : (nb078_alpha_dummy_471) ∉ (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_460))).fv) := by
  simpa only [nb078_alpha_dummy_471] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_460))).fv) 0

theorem nb078_fresh_695 : (nb078_alpha_dummy_467) ∉ (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) := by
  simpa only [nb078_alpha_dummy_467] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) 0

theorem nb078_fresh_696 : (nb078_alpha_dummy_473) ∉ (((Class.cv (nb078_alpha_dummy_461))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) := by
  simpa only [nb078_alpha_dummy_473] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_461))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) 0

theorem nb078_fresh_697 (g : Var) : (nb078_alpha_dummy_472 g) ∉ (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_463 g))).fv) := by
  simpa only [nb078_alpha_dummy_472] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_463 g))).fv) 0

theorem nb078_fresh_698 (g : Var) : (nb078_alpha_dummy_468 g) ∉ (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) := by
  simpa only [nb078_alpha_dummy_468] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) 0

theorem nb078_fresh_699 (g : Var) : (nb078_alpha_dummy_474 g) ∉ (((Class.cv (nb078_alpha_dummy_464 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) := by
  simpa only [nb078_alpha_dummy_474] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_464 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) 0

theorem nb078_fresh_700 : (nb078_alpha_dummy_485) ∉ (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) := by
  simpa only [nb078_alpha_dummy_485] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) 0

theorem nb078_fresh_701 : (nb078_alpha_dummy_486) ∉ (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) := by
  simpa only [nb078_alpha_dummy_486] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) 1

theorem nb078_distinct_702 : (nb078_alpha_dummy_485) ≠ (nb078_alpha_dummy_486) := by
  simpa only [nb078_alpha_dummy_485, nb078_alpha_dummy_486] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_703 (g : Var) : (nb078_alpha_dummy_487 g) ∉ (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) := by
  simpa only [nb078_alpha_dummy_487] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
