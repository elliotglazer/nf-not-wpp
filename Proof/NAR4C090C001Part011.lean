import NAR4C090C001Part010

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

theorem nb090_fresh_542 (A : Class) : (nb090_alpha_dummy_525 A) ∉ (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_525] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_543 (A : Class) : (nb090_alpha_dummy_523 A) ≠ (nb090_alpha_dummy_524 A) := by
  simpa only [nb090_alpha_dummy_523, nb090_alpha_dummy_524] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_544 (A : Class) : (nb090_alpha_dummy_523 A) ≠ (nb090_alpha_dummy_525 A) := by
  simpa only [nb090_alpha_dummy_523, nb090_alpha_dummy_525] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_545 (A : Class) : (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_525 A) := by
  simpa only [nb090_alpha_dummy_524, nb090_alpha_dummy_525] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_546 (h : Var) : (nb090_alpha_dummy_526 h) ∉ (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_526] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_547 (h : Var) : (nb090_alpha_dummy_527 h) ∉ (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_527] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_548 (h : Var) : (nb090_alpha_dummy_528 h) ∉ (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_528] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_549 (h : Var) : (nb090_alpha_dummy_526 h) ≠ (nb090_alpha_dummy_527 h) := by
  simpa only [nb090_alpha_dummy_526, nb090_alpha_dummy_527] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_550 (h : Var) : (nb090_alpha_dummy_526 h) ≠ (nb090_alpha_dummy_528 h) := by
  simpa only [nb090_alpha_dummy_526, nb090_alpha_dummy_528] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_551 (h : Var) : (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_528 h) := by
  simpa only [nb090_alpha_dummy_527, nb090_alpha_dummy_528] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_552 (A : Class) : (nb090_alpha_dummy_535 A) ∉ (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_524 A))).fv) := by
  simpa only [nb090_alpha_dummy_535] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_524 A))).fv) 0

theorem nb090_fresh_553 (A : Class) : (nb090_alpha_dummy_531 A) ∉ (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) := by
  simpa only [nb090_alpha_dummy_531] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) 0

theorem nb090_fresh_554 (A : Class) : (nb090_alpha_dummy_537 A) ∉ (((Class.cv (nb090_alpha_dummy_525 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) := by
  simpa only [nb090_alpha_dummy_537] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_525 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) 0

theorem nb090_fresh_555 (h : Var) : (nb090_alpha_dummy_536 h) ∉ (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_527 h))).fv) := by
  simpa only [nb090_alpha_dummy_536] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_527 h))).fv) 0

theorem nb090_fresh_556 (h : Var) : (nb090_alpha_dummy_532 h) ∉ (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) := by
  simpa only [nb090_alpha_dummy_532] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) 0

theorem nb090_fresh_557 (h : Var) : (nb090_alpha_dummy_538 h) ∉ (((Class.cv (nb090_alpha_dummy_528 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) := by
  simpa only [nb090_alpha_dummy_538] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_528 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) 0

theorem nb090_fresh_558 (A : Class) : (nb090_alpha_dummy_553 A) ∉ (((Class.cv (nb090_alpha_dummy_546 A))).fv) := by
  simpa only [nb090_alpha_dummy_553] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_546 A))).fv) 0

theorem nb090_fresh_559 (A : Class) : (nb090_alpha_dummy_554 A) ∉ (((Class.cv (nb090_alpha_dummy_546 A))).fv) := by
  simpa only [nb090_alpha_dummy_554] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_546 A))).fv) 1

theorem nb090_distinct_560 (A : Class) : (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_554 A) := by
  simpa only [nb090_alpha_dummy_553, nb090_alpha_dummy_554] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_546 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_561 (h : Var) : (nb090_alpha_dummy_555 h) ∉ (((Class.cv (nb090_alpha_dummy_548 h))).fv) := by
  simpa only [nb090_alpha_dummy_555] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_548 h))).fv) 0

theorem nb090_fresh_562 (h : Var) : (nb090_alpha_dummy_556 h) ∉ (((Class.cv (nb090_alpha_dummy_548 h))).fv) := by
  simpa only [nb090_alpha_dummy_556] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_548 h))).fv) 1

theorem nb090_distinct_563 (h : Var) : (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_556 h) := by
  simpa only [nb090_alpha_dummy_555, nb090_alpha_dummy_556] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_548 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_564 (A : Class) : (nb090_alpha_dummy_559 A) ∉ (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_559] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_565 (A : Class) : (nb090_alpha_dummy_560 A) ∉ (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_560] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_566 (A : Class) : (nb090_alpha_dummy_561 A) ∉ (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_561] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_567 (A : Class) : (nb090_alpha_dummy_559 A) ≠ (nb090_alpha_dummy_560 A) := by
  simpa only [nb090_alpha_dummy_559, nb090_alpha_dummy_560] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_568 (A : Class) : (nb090_alpha_dummy_559 A) ≠ (nb090_alpha_dummy_561 A) := by
  simpa only [nb090_alpha_dummy_559, nb090_alpha_dummy_561] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_569 (A : Class) : (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_561 A) := by
  simpa only [nb090_alpha_dummy_560, nb090_alpha_dummy_561] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_570 (h : Var) : (nb090_alpha_dummy_562 h) ∉ (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_562] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_571 (h : Var) : (nb090_alpha_dummy_563 h) ∉ (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_563] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_572 (h : Var) : (nb090_alpha_dummy_564 h) ∉ (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_564] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_573 (h : Var) : (nb090_alpha_dummy_562 h) ≠ (nb090_alpha_dummy_563 h) := by
  simpa only [nb090_alpha_dummy_562, nb090_alpha_dummy_563] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_574 (h : Var) : (nb090_alpha_dummy_562 h) ≠ (nb090_alpha_dummy_564 h) := by
  simpa only [nb090_alpha_dummy_562, nb090_alpha_dummy_564] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_575 (h : Var) : (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_564 h) := by
  simpa only [nb090_alpha_dummy_563, nb090_alpha_dummy_564] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_576 (A : Class) : (nb090_alpha_dummy_571 A) ∉ (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_560 A))).fv) := by
  simpa only [nb090_alpha_dummy_571] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_560 A))).fv) 0

theorem nb090_fresh_577 (A : Class) : (nb090_alpha_dummy_567 A) ∉ (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) := by
  simpa only [nb090_alpha_dummy_567] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) 0

theorem nb090_fresh_578 (A : Class) : (nb090_alpha_dummy_573 A) ∉ (((Class.cv (nb090_alpha_dummy_561 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) := by
  simpa only [nb090_alpha_dummy_573] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_561 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) 0

theorem nb090_fresh_579 (h : Var) : (nb090_alpha_dummy_572 h) ∉ (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_563 h))).fv) := by
  simpa only [nb090_alpha_dummy_572] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_563 h))).fv) 0

theorem nb090_fresh_580 (h : Var) : (nb090_alpha_dummy_568 h) ∉ (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) := by
  simpa only [nb090_alpha_dummy_568] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) 0

theorem nb090_fresh_581 (h : Var) : (nb090_alpha_dummy_574 h) ∉ (((Class.cv (nb090_alpha_dummy_564 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) := by
  simpa only [nb090_alpha_dummy_574] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_564 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) 0

theorem nb090_fresh_582 (A : Class) : (nb090_alpha_dummy_589 A) ∉ (((Class.cv (nb090_alpha_dummy_582 A))).fv) := by
  simpa only [nb090_alpha_dummy_589] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_582 A))).fv) 0

theorem nb090_fresh_583 (A : Class) : (nb090_alpha_dummy_590 A) ∉ (((Class.cv (nb090_alpha_dummy_582 A))).fv) := by
  simpa only [nb090_alpha_dummy_590] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_582 A))).fv) 1

theorem nb090_distinct_584 (A : Class) : (nb090_alpha_dummy_589 A) ≠ (nb090_alpha_dummy_590 A) := by
  simpa only [nb090_alpha_dummy_589, nb090_alpha_dummy_590] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_582 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_585 (h : Var) : (nb090_alpha_dummy_591 h) ∉ (((Class.cv (nb090_alpha_dummy_584 h))).fv) := by
  simpa only [nb090_alpha_dummy_591] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_584 h))).fv) 0

theorem nb090_fresh_586 (h : Var) : (nb090_alpha_dummy_592 h) ∉ (((Class.cv (nb090_alpha_dummy_584 h))).fv) := by
  simpa only [nb090_alpha_dummy_592] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_584 h))).fv) 1

theorem nb090_distinct_587 (h : Var) : (nb090_alpha_dummy_591 h) ≠ (nb090_alpha_dummy_592 h) := by
  simpa only [nb090_alpha_dummy_591, nb090_alpha_dummy_592] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_584 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_588 (A : Class) : (nb090_alpha_dummy_595 A) ∉ (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_595] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_589 (A : Class) : (nb090_alpha_dummy_596 A) ∉ (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_596] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_590 (A : Class) : (nb090_alpha_dummy_597 A) ∉ (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_597] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_591 (A : Class) : (nb090_alpha_dummy_595 A) ≠ (nb090_alpha_dummy_596 A) := by
  simpa only [nb090_alpha_dummy_595, nb090_alpha_dummy_596] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_592 (A : Class) : (nb090_alpha_dummy_595 A) ≠ (nb090_alpha_dummy_597 A) := by
  simpa only [nb090_alpha_dummy_595, nb090_alpha_dummy_597] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_593 (A : Class) : (nb090_alpha_dummy_596 A) ≠ (nb090_alpha_dummy_597 A) := by
  simpa only [nb090_alpha_dummy_596, nb090_alpha_dummy_597] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_594 (h : Var) : (nb090_alpha_dummy_598 h) ∉ (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_598] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_595 (h : Var) : (nb090_alpha_dummy_599 h) ∉ (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_599] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_596 (h : Var) : (nb090_alpha_dummy_600 h) ∉ (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_600] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_597 (h : Var) : (nb090_alpha_dummy_598 h) ≠ (nb090_alpha_dummy_599 h) := by
  simpa only [nb090_alpha_dummy_598, nb090_alpha_dummy_599] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_598 (h : Var) : (nb090_alpha_dummy_598 h) ≠ (nb090_alpha_dummy_600 h) := by
  simpa only [nb090_alpha_dummy_598, nb090_alpha_dummy_600] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_599 (h : Var) : (nb090_alpha_dummy_599 h) ≠ (nb090_alpha_dummy_600 h) := by
  simpa only [nb090_alpha_dummy_599, nb090_alpha_dummy_600] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_600 (A : Class) : (nb090_alpha_dummy_607 A) ∉ (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_596 A))).fv) := by
  simpa only [nb090_alpha_dummy_607] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_596 A))).fv) 0

theorem nb090_fresh_601 (A : Class) : (nb090_alpha_dummy_603 A) ∉ (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) := by
  simpa only [nb090_alpha_dummy_603] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) 0

theorem nb090_fresh_602 (A : Class) : (nb090_alpha_dummy_609 A) ∉ (((Class.cv (nb090_alpha_dummy_597 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) := by
  simpa only [nb090_alpha_dummy_609] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_597 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) 0

theorem nb090_fresh_603 (h : Var) : (nb090_alpha_dummy_608 h) ∉ (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_599 h))).fv) := by
  simpa only [nb090_alpha_dummy_608] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_599 h))).fv) 0

theorem nb090_fresh_604 (h : Var) : (nb090_alpha_dummy_604 h) ∉ (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) := by
  simpa only [nb090_alpha_dummy_604] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) 0

theorem nb090_fresh_605 (h : Var) : (nb090_alpha_dummy_610 h) ∉ (((Class.cv (nb090_alpha_dummy_600 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) := by
  simpa only [nb090_alpha_dummy_610] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_600 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) 0

theorem nb090_fresh_606 (A : Class) : (nb090_alpha_dummy_625 A) ∉ (((Class.cv (nb090_alpha_dummy_618 A))).fv) := by
  simpa only [nb090_alpha_dummy_625] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_618 A))).fv) 0

theorem nb090_fresh_607 (A : Class) : (nb090_alpha_dummy_626 A) ∉ (((Class.cv (nb090_alpha_dummy_618 A))).fv) := by
  simpa only [nb090_alpha_dummy_626] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_618 A))).fv) 1

theorem nb090_distinct_608 (A : Class) : (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_626 A) := by
  simpa only [nb090_alpha_dummy_625, nb090_alpha_dummy_626] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_618 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_609 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_627 v u h) ∉ (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_627] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) 0

theorem nb090_fresh_610 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_628 v u h) ∉ (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_628] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) 1

theorem nb090_distinct_611 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_628 v u h) := by
  simpa only [nb090_alpha_dummy_627, nb090_alpha_dummy_628] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_612 (A : Class) : (nb090_alpha_dummy_631 A) ∉ (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_631] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_613 (A : Class) : (nb090_alpha_dummy_632 A) ∉ (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_632] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_614 (A : Class) : (nb090_alpha_dummy_633 A) ∉ (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_633] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_615 (A : Class) : (nb090_alpha_dummy_631 A) ≠ (nb090_alpha_dummy_632 A) := by
  simpa only [nb090_alpha_dummy_631, nb090_alpha_dummy_632] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_616 (A : Class) : (nb090_alpha_dummy_631 A) ≠ (nb090_alpha_dummy_633 A) := by
  simpa only [nb090_alpha_dummy_631, nb090_alpha_dummy_633] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_617 (A : Class) : (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_633 A) := by
  simpa only [nb090_alpha_dummy_632, nb090_alpha_dummy_633] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_618 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_634 v u h) ∉ (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_634] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_619 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_635 v u h) ∉ (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_635] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_620 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_636 v u h) ∉ (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_636] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_621 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_634 v u h) ≠ (nb090_alpha_dummy_635 v u h) := by
  simpa only [nb090_alpha_dummy_634, nb090_alpha_dummy_635] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_622 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_634 v u h) ≠ (nb090_alpha_dummy_636 v u h) := by
  simpa only [nb090_alpha_dummy_634, nb090_alpha_dummy_636] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_623 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_636 v u h) := by
  simpa only [nb090_alpha_dummy_635, nb090_alpha_dummy_636] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_624 (A : Class) : (nb090_alpha_dummy_643 A) ∉ (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_632 A))).fv) := by
  simpa only [nb090_alpha_dummy_643] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_632 A))).fv) 0

theorem nb090_fresh_625 (A : Class) : (nb090_alpha_dummy_639 A) ∉ (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) := by
  simpa only [nb090_alpha_dummy_639] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) 0

theorem nb090_fresh_626 (A : Class) : (nb090_alpha_dummy_645 A) ∉ (((Class.cv (nb090_alpha_dummy_633 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) := by
  simpa only [nb090_alpha_dummy_645] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_633 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) 0

theorem nb090_fresh_627 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_644 v u h) ∉ (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_635 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_644] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_635 v u h))).fv) 0

theorem nb090_fresh_628 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_640 v u h) ∉ (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_640] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) 0

theorem nb090_fresh_629 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_646 v u h) ∉ (((Class.cv (nb090_alpha_dummy_636 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_646] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_636 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) 0

theorem nb090_fresh_630 (A : Class) : (nb090_alpha_dummy_697 A) ∉ (((Class.cv (nb090_alpha_dummy_655 A))).fv) := by
  simpa only [nb090_alpha_dummy_697] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_655 A))).fv) 0

theorem nb090_fresh_631 (u : Var) : (nb090_alpha_dummy_698 u) ∉ (((Class.cv (nb090_alpha_dummy_656 u))).fv) := by
  simpa only [nb090_alpha_dummy_698] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_656 u))).fv) 0

theorem nb090_fresh_632 (A : Class) : (nb090_alpha_dummy_669 A) ∉ (((Class.cv (nb090_alpha_dummy_662 A))).fv) := by
  simpa only [nb090_alpha_dummy_669] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_662 A))).fv) 0

theorem nb090_fresh_633 (A : Class) : (nb090_alpha_dummy_670 A) ∉ (((Class.cv (nb090_alpha_dummy_662 A))).fv) := by
  simpa only [nb090_alpha_dummy_670] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_662 A))).fv) 1

theorem nb090_distinct_634 (A : Class) : (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_670 A) := by
  simpa only [nb090_alpha_dummy_669, nb090_alpha_dummy_670] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_662 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_635 (u : Var) : (nb090_alpha_dummy_671 u) ∉ (((Class.cv (nb090_alpha_dummy_664 u))).fv) := by
  simpa only [nb090_alpha_dummy_671] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_664 u))).fv) 0

theorem nb090_fresh_636 (u : Var) : (nb090_alpha_dummy_672 u) ∉ (((Class.cv (nb090_alpha_dummy_664 u))).fv) := by
  simpa only [nb090_alpha_dummy_672] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_664 u))).fv) 1

theorem nb090_distinct_637 (u : Var) : (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_672 u) := by
  simpa only [nb090_alpha_dummy_671, nb090_alpha_dummy_672] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_664 u))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_638 (A : Class) : (nb090_alpha_dummy_675 A) ∉ (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_675] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_639 (A : Class) : (nb090_alpha_dummy_676 A) ∉ (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_676] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_640 (A : Class) : (nb090_alpha_dummy_677 A) ∉ (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_677] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_641 (A : Class) : (nb090_alpha_dummy_675 A) ≠ (nb090_alpha_dummy_676 A) := by
  simpa only [nb090_alpha_dummy_675, nb090_alpha_dummy_676] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_642 (A : Class) : (nb090_alpha_dummy_675 A) ≠ (nb090_alpha_dummy_677 A) := by
  simpa only [nb090_alpha_dummy_675, nb090_alpha_dummy_677] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_643 (A : Class) : (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_677 A) := by
  simpa only [nb090_alpha_dummy_676, nb090_alpha_dummy_677] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_644 (u : Var) : (nb090_alpha_dummy_678 u) ∉ (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_678] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_645 (u : Var) : (nb090_alpha_dummy_679 u) ∉ (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_679] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_646 (u : Var) : (nb090_alpha_dummy_680 u) ∉ (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_680] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_647 (u : Var) : (nb090_alpha_dummy_678 u) ≠ (nb090_alpha_dummy_679 u) := by
  simpa only [nb090_alpha_dummy_678, nb090_alpha_dummy_679] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_648 (u : Var) : (nb090_alpha_dummy_678 u) ≠ (nb090_alpha_dummy_680 u) := by
  simpa only [nb090_alpha_dummy_678, nb090_alpha_dummy_680] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_649 (u : Var) : (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_680 u) := by
  simpa only [nb090_alpha_dummy_679, nb090_alpha_dummy_680] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_650 (A : Class) : (nb090_alpha_dummy_687 A) ∉ (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_676 A))).fv) := by
  simpa only [nb090_alpha_dummy_687] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_676 A))).fv) 0

theorem nb090_fresh_651 (A : Class) : (nb090_alpha_dummy_683 A) ∉ (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) := by
  simpa only [nb090_alpha_dummy_683] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) 0

theorem nb090_fresh_652 (A : Class) : (nb090_alpha_dummy_689 A) ∉ (((Class.cv (nb090_alpha_dummy_677 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) := by
  simpa only [nb090_alpha_dummy_689] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_677 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) 0

theorem nb090_fresh_653 (u : Var) : (nb090_alpha_dummy_688 u) ∉ (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_679 u))).fv) := by
  simpa only [nb090_alpha_dummy_688] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_679 u))).fv) 0

theorem nb090_fresh_654 (u : Var) : (nb090_alpha_dummy_684 u) ∉ (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) := by
  simpa only [nb090_alpha_dummy_684] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) 0

theorem nb090_fresh_655 (u : Var) : (nb090_alpha_dummy_690 u) ∉ (((Class.cv (nb090_alpha_dummy_680 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) := by
  simpa only [nb090_alpha_dummy_690] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_680 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) 0

theorem nb090_fresh_656 (A : Class) : (nb090_alpha_dummy_753 A) ∉ (((Class.cv (nb090_alpha_dummy_700 A))).fv) := by
  simpa only [nb090_alpha_dummy_753] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_700 A))).fv) 0

theorem nb090_fresh_657 (A : Class) : (nb090_alpha_dummy_754 A) ∉ (((Class.cv (nb090_alpha_dummy_700 A))).fv) := by
  simpa only [nb090_alpha_dummy_754] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_700 A))).fv) 1

theorem nb090_distinct_658 (A : Class) : (nb090_alpha_dummy_753 A) ≠ (nb090_alpha_dummy_754 A) := by
  simpa only [nb090_alpha_dummy_753, nb090_alpha_dummy_754] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_700 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_659 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_755 v u h) ∉ (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_755] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) 0

theorem nb090_fresh_660 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_756 v u h) ∉ (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_756] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) 1

theorem nb090_distinct_661 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_755 v u h) ≠ (nb090_alpha_dummy_756 v u h) := by
  simpa only [nb090_alpha_dummy_755, nb090_alpha_dummy_756] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_662 (A : Class) : (nb090_alpha_dummy_751 A) ∉ (((Class.cv (nb090_alpha_dummy_709 A))).fv) := by
  simpa only [nb090_alpha_dummy_751] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_709 A))).fv) 0

theorem nb090_fresh_663 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_752 v u h) ∉ (((Class.cv (nb090_alpha_dummy_710 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_752] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_710 v u h))).fv) 0

theorem nb090_fresh_664 (A : Class) : (nb090_alpha_dummy_723 A) ∉ (((Class.cv (nb090_alpha_dummy_716 A))).fv) := by
  simpa only [nb090_alpha_dummy_723] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_716 A))).fv) 0

theorem nb090_fresh_665 (A : Class) : (nb090_alpha_dummy_724 A) ∉ (((Class.cv (nb090_alpha_dummy_716 A))).fv) := by
  simpa only [nb090_alpha_dummy_724] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_716 A))).fv) 1

theorem nb090_distinct_666 (A : Class) : (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_724 A) := by
  simpa only [nb090_alpha_dummy_723, nb090_alpha_dummy_724] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_716 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_667 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_725 v u h) ∉ (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_725] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) 0

theorem nb090_fresh_668 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_726 v u h) ∉ (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_726] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) 1

theorem nb090_distinct_669 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_726 v u h) := by
  simpa only [nb090_alpha_dummy_725, nb090_alpha_dummy_726] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_670 (A : Class) : (nb090_alpha_dummy_729 A) ∉ (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_729] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_671 (A : Class) : (nb090_alpha_dummy_730 A) ∉ (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_730] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_672 (A : Class) : (nb090_alpha_dummy_731 A) ∉ (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_731] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_673 (A : Class) : (nb090_alpha_dummy_729 A) ≠ (nb090_alpha_dummy_730 A) := by
  simpa only [nb090_alpha_dummy_729, nb090_alpha_dummy_730] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_674 (A : Class) : (nb090_alpha_dummy_729 A) ≠ (nb090_alpha_dummy_731 A) := by
  simpa only [nb090_alpha_dummy_729, nb090_alpha_dummy_731] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_675 (A : Class) : (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_731 A) := by
  simpa only [nb090_alpha_dummy_730, nb090_alpha_dummy_731] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_676 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_732 v u h) ∉ (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_732] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_677 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_733 v u h) ∉ (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_733] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_678 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_734 v u h) ∉ (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_734] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_679 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_732 v u h) ≠ (nb090_alpha_dummy_733 v u h) := by
  simpa only [nb090_alpha_dummy_732, nb090_alpha_dummy_733] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_680 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_732 v u h) ≠ (nb090_alpha_dummy_734 v u h) := by
  simpa only [nb090_alpha_dummy_732, nb090_alpha_dummy_734] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_681 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_734 v u h) := by
  simpa only [nb090_alpha_dummy_733, nb090_alpha_dummy_734] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_682 (A : Class) : (nb090_alpha_dummy_741 A) ∉ (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_730 A))).fv) := by
  simpa only [nb090_alpha_dummy_741] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_730 A))).fv) 0

theorem nb090_fresh_683 (A : Class) : (nb090_alpha_dummy_737 A) ∉ (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) := by
  simpa only [nb090_alpha_dummy_737] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) 0

theorem nb090_fresh_684 (A : Class) : (nb090_alpha_dummy_743 A) ∉ (((Class.cv (nb090_alpha_dummy_731 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) := by
  simpa only [nb090_alpha_dummy_743] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_731 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) 0

theorem nb090_fresh_685 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_742 v u h) ∉ (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_733 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_742] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_733 v u h))).fv) 0

theorem nb090_fresh_686 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_738 v u h) ∉ (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_738] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) 0

theorem nb090_fresh_687 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_744 v u h) ∉ (((Class.cv (nb090_alpha_dummy_734 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_744] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_734 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) 0

theorem nb090_fresh_688 (A : Class) : (nb090_alpha_dummy_759 A) ∉ (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_759] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_689 (A : Class) : (nb090_alpha_dummy_760 A) ∉ (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_760] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_690 (A : Class) : (nb090_alpha_dummy_761 A) ∉ (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_761] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_691 (A : Class) : (nb090_alpha_dummy_759 A) ≠ (nb090_alpha_dummy_760 A) := by
  simpa only [nb090_alpha_dummy_759, nb090_alpha_dummy_760] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
