import NAR4C078C001Part014

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

theorem nb078_fresh_704 (g : Var) : (nb078_alpha_dummy_488 g) ∉ (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) := by
  simpa only [nb078_alpha_dummy_488] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) 1

theorem nb078_distinct_705 (g : Var) : (nb078_alpha_dummy_487 g) ≠ (nb078_alpha_dummy_488 g) := by
  simpa only [nb078_alpha_dummy_487, nb078_alpha_dummy_488] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_706 : (nb078_alpha_dummy_493) ∉ (((Class.cv (nb078_alpha_dummy_486))).fv) := by
  simpa only [nb078_alpha_dummy_493] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_486))).fv) 0

theorem nb078_fresh_707 : (nb078_alpha_dummy_494) ∉ (((Class.cv (nb078_alpha_dummy_486))).fv) := by
  simpa only [nb078_alpha_dummy_494] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_486))).fv) 1

theorem nb078_distinct_708 : (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_494) := by
  simpa only [nb078_alpha_dummy_493, nb078_alpha_dummy_494] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_486))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_709 (g : Var) : (nb078_alpha_dummy_495 g) ∉ (((Class.cv (nb078_alpha_dummy_488 g))).fv) := by
  simpa only [nb078_alpha_dummy_495] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_488 g))).fv) 0

theorem nb078_fresh_710 (g : Var) : (nb078_alpha_dummy_496 g) ∉ (((Class.cv (nb078_alpha_dummy_488 g))).fv) := by
  simpa only [nb078_alpha_dummy_496] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_488 g))).fv) 1

theorem nb078_distinct_711 (g : Var) : (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_496 g) := by
  simpa only [nb078_alpha_dummy_495, nb078_alpha_dummy_496] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_488 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_712 : (nb078_alpha_dummy_499) ∉ (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_499] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_713 : (nb078_alpha_dummy_500) ∉ (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_500] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_714 : (nb078_alpha_dummy_501) ∉ (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_501] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_715 : (nb078_alpha_dummy_499) ≠ (nb078_alpha_dummy_500) := by
  simpa only [nb078_alpha_dummy_499, nb078_alpha_dummy_500] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_716 : (nb078_alpha_dummy_499) ≠ (nb078_alpha_dummy_501) := by
  simpa only [nb078_alpha_dummy_499, nb078_alpha_dummy_501] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_717 : (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_501) := by
  simpa only [nb078_alpha_dummy_500, nb078_alpha_dummy_501] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_718 (g : Var) : (nb078_alpha_dummy_502 g) ∉ (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_502] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_719 (g : Var) : (nb078_alpha_dummy_503 g) ∉ (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_503] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_720 (g : Var) : (nb078_alpha_dummy_504 g) ∉ (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_504] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_721 (g : Var) : (nb078_alpha_dummy_502 g) ≠ (nb078_alpha_dummy_503 g) := by
  simpa only [nb078_alpha_dummy_502, nb078_alpha_dummy_503] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_722 (g : Var) : (nb078_alpha_dummy_502 g) ≠ (nb078_alpha_dummy_504 g) := by
  simpa only [nb078_alpha_dummy_502, nb078_alpha_dummy_504] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_723 (g : Var) : (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_504 g) := by
  simpa only [nb078_alpha_dummy_503, nb078_alpha_dummy_504] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_724 : (nb078_alpha_dummy_511) ∉ (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_500))).fv) := by
  simpa only [nb078_alpha_dummy_511] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_500))).fv) 0

theorem nb078_fresh_725 : (nb078_alpha_dummy_507) ∉ (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) := by
  simpa only [nb078_alpha_dummy_507] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) 0

theorem nb078_fresh_726 : (nb078_alpha_dummy_513) ∉ (((Class.cv (nb078_alpha_dummy_501))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) := by
  simpa only [nb078_alpha_dummy_513] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_501))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) 0

theorem nb078_fresh_727 (g : Var) : (nb078_alpha_dummy_512 g) ∉ (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_503 g))).fv) := by
  simpa only [nb078_alpha_dummy_512] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_503 g))).fv) 0

theorem nb078_fresh_728 (g : Var) : (nb078_alpha_dummy_508 g) ∉ (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) := by
  simpa only [nb078_alpha_dummy_508] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) 0

theorem nb078_fresh_729 (g : Var) : (nb078_alpha_dummy_514 g) ∉ (((Class.cv (nb078_alpha_dummy_504 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) := by
  simpa only [nb078_alpha_dummy_514] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_504 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) 0

theorem nb078_fresh_730 : (nb078_alpha_dummy_529) ∉ (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) := by
  simpa only [nb078_alpha_dummy_529] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) 0

theorem nb078_fresh_731 : (nb078_alpha_dummy_530) ∉ (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) := by
  simpa only [nb078_alpha_dummy_530] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) 1

theorem nb078_distinct_732 : (nb078_alpha_dummy_529) ≠ (nb078_alpha_dummy_530) := by
  simpa only [nb078_alpha_dummy_529, nb078_alpha_dummy_530] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_733 (g : Var) : (nb078_alpha_dummy_531 g) ∉ (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) := by
  simpa only [nb078_alpha_dummy_531] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) 0

theorem nb078_fresh_734 (g : Var) : (nb078_alpha_dummy_532 g) ∉ (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) := by
  simpa only [nb078_alpha_dummy_532] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) 1

theorem nb078_distinct_735 (g : Var) : (nb078_alpha_dummy_531 g) ≠ (nb078_alpha_dummy_532 g) := by
  simpa only [nb078_alpha_dummy_531, nb078_alpha_dummy_532] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_736 : (nb078_alpha_dummy_537) ∉ (((Class.cv (nb078_alpha_dummy_530))).fv) := by
  simpa only [nb078_alpha_dummy_537] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_530))).fv) 0

theorem nb078_fresh_737 : (nb078_alpha_dummy_538) ∉ (((Class.cv (nb078_alpha_dummy_530))).fv) := by
  simpa only [nb078_alpha_dummy_538] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_530))).fv) 1

theorem nb078_distinct_738 : (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_538) := by
  simpa only [nb078_alpha_dummy_537, nb078_alpha_dummy_538] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_530))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_739 (g : Var) : (nb078_alpha_dummy_539 g) ∉ (((Class.cv (nb078_alpha_dummy_532 g))).fv) := by
  simpa only [nb078_alpha_dummy_539] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_532 g))).fv) 0

theorem nb078_fresh_740 (g : Var) : (nb078_alpha_dummy_540 g) ∉ (((Class.cv (nb078_alpha_dummy_532 g))).fv) := by
  simpa only [nb078_alpha_dummy_540] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_532 g))).fv) 1

theorem nb078_distinct_741 (g : Var) : (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_540 g) := by
  simpa only [nb078_alpha_dummy_539, nb078_alpha_dummy_540] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_532 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_742 : (nb078_alpha_dummy_543) ∉ (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_543] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_743 : (nb078_alpha_dummy_544) ∉ (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_544] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_744 : (nb078_alpha_dummy_545) ∉ (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_545] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_745 : (nb078_alpha_dummy_543) ≠ (nb078_alpha_dummy_544) := by
  simpa only [nb078_alpha_dummy_543, nb078_alpha_dummy_544] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_746 : (nb078_alpha_dummy_543) ≠ (nb078_alpha_dummy_545) := by
  simpa only [nb078_alpha_dummy_543, nb078_alpha_dummy_545] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_747 : (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_545) := by
  simpa only [nb078_alpha_dummy_544, nb078_alpha_dummy_545] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_748 (g : Var) : (nb078_alpha_dummy_546 g) ∉ (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_546] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_749 (g : Var) : (nb078_alpha_dummy_547 g) ∉ (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_547] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_750 (g : Var) : (nb078_alpha_dummy_548 g) ∉ (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_548] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_751 (g : Var) : (nb078_alpha_dummy_546 g) ≠ (nb078_alpha_dummy_547 g) := by
  simpa only [nb078_alpha_dummy_546, nb078_alpha_dummy_547] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_752 (g : Var) : (nb078_alpha_dummy_546 g) ≠ (nb078_alpha_dummy_548 g) := by
  simpa only [nb078_alpha_dummy_546, nb078_alpha_dummy_548] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_753 (g : Var) : (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_548 g) := by
  simpa only [nb078_alpha_dummy_547, nb078_alpha_dummy_548] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_754 : (nb078_alpha_dummy_555) ∉ (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_544))).fv) := by
  simpa only [nb078_alpha_dummy_555] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_544))).fv) 0

theorem nb078_fresh_755 : (nb078_alpha_dummy_551) ∉ (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) := by
  simpa only [nb078_alpha_dummy_551] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) 0

theorem nb078_fresh_756 : (nb078_alpha_dummy_557) ∉ (((Class.cv (nb078_alpha_dummy_545))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) := by
  simpa only [nb078_alpha_dummy_557] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_545))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) 0

theorem nb078_fresh_757 (g : Var) : (nb078_alpha_dummy_556 g) ∉ (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_547 g))).fv) := by
  simpa only [nb078_alpha_dummy_556] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_547 g))).fv) 0

theorem nb078_fresh_758 (g : Var) : (nb078_alpha_dummy_552 g) ∉ (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) := by
  simpa only [nb078_alpha_dummy_552] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) 0

theorem nb078_fresh_759 (g : Var) : (nb078_alpha_dummy_558 g) ∉ (((Class.cv (nb078_alpha_dummy_548 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) := by
  simpa only [nb078_alpha_dummy_558] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_548 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) 0

theorem nb078_fresh_760 : (nb078_alpha_dummy_577) ∉ (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) := by
  simpa only [nb078_alpha_dummy_577] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 0

theorem nb078_fresh_761 : (nb078_alpha_dummy_578) ∉ (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) := by
  simpa only [nb078_alpha_dummy_578] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 1

theorem nb078_distinct_762 : (nb078_alpha_dummy_577) ≠ (nb078_alpha_dummy_578) := by
  simpa only [nb078_alpha_dummy_577, nb078_alpha_dummy_578] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_763 : (nb078_alpha_dummy_613) ∉ (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) := by
  simpa only [nb078_alpha_dummy_613] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) 0

theorem nb078_fresh_764 : (nb078_alpha_dummy_614) ∉ (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) := by
  simpa only [nb078_alpha_dummy_614] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) 1

theorem nb078_distinct_765 : (nb078_alpha_dummy_613) ≠ (nb078_alpha_dummy_614) := by
  simpa only [nb078_alpha_dummy_613, nb078_alpha_dummy_614] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_766 : (nb078_alpha_dummy_727) ∉ (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) := by
  simpa only [nb078_alpha_dummy_727] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 0

theorem nb078_fresh_767 : (nb078_alpha_dummy_728) ∉ (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) := by
  simpa only [nb078_alpha_dummy_728] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 1

theorem nb078_distinct_768 : (nb078_alpha_dummy_727) ≠ (nb078_alpha_dummy_728) := by
  simpa only [nb078_alpha_dummy_727, nb078_alpha_dummy_728] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_769 (g : Var) : (nb078_alpha_dummy_579 g) ∉ (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) := by
  simpa only [nb078_alpha_dummy_579] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) 0

theorem nb078_fresh_770 (g : Var) : (nb078_alpha_dummy_580 g) ∉ (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) := by
  simpa only [nb078_alpha_dummy_580] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) 1

theorem nb078_distinct_771 (g : Var) : (nb078_alpha_dummy_579 g) ≠ (nb078_alpha_dummy_580 g) := by
  simpa only [nb078_alpha_dummy_579, nb078_alpha_dummy_580] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_772 (g : Var) : (nb078_alpha_dummy_615 g) ∉ (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) := by
  simpa only [nb078_alpha_dummy_615] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) 0

theorem nb078_fresh_773 (g : Var) : (nb078_alpha_dummy_616 g) ∉ (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) := by
  simpa only [nb078_alpha_dummy_616] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) 1

theorem nb078_distinct_774 (g : Var) : (nb078_alpha_dummy_615 g) ≠ (nb078_alpha_dummy_616 g) := by
  simpa only [nb078_alpha_dummy_615, nb078_alpha_dummy_616] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_775 (g : Var) : (nb078_alpha_dummy_729 g) ∉ (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) := by
  simpa only [nb078_alpha_dummy_729] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) 0

theorem nb078_fresh_776 (g : Var) : (nb078_alpha_dummy_730 g) ∉ (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) := by
  simpa only [nb078_alpha_dummy_730] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) 1

theorem nb078_distinct_777 (g : Var) : (nb078_alpha_dummy_729 g) ≠ (nb078_alpha_dummy_730 g) := by
  simpa only [nb078_alpha_dummy_729, nb078_alpha_dummy_730] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_778 : (nb078_alpha_dummy_585) ∉ (((Class.cv (nb078_alpha_dummy_578))).fv) := by
  simpa only [nb078_alpha_dummy_585] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_578))).fv) 0

theorem nb078_fresh_779 : (nb078_alpha_dummy_586) ∉ (((Class.cv (nb078_alpha_dummy_578))).fv) := by
  simpa only [nb078_alpha_dummy_586] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_578))).fv) 1

theorem nb078_distinct_780 : (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_586) := by
  simpa only [nb078_alpha_dummy_585, nb078_alpha_dummy_586] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_578))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_781 (g : Var) : (nb078_alpha_dummy_587 g) ∉ (((Class.cv (nb078_alpha_dummy_580 g))).fv) := by
  simpa only [nb078_alpha_dummy_587] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_580 g))).fv) 0

theorem nb078_fresh_782 (g : Var) : (nb078_alpha_dummy_588 g) ∉ (((Class.cv (nb078_alpha_dummy_580 g))).fv) := by
  simpa only [nb078_alpha_dummy_588] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_580 g))).fv) 1

theorem nb078_distinct_783 (g : Var) : (nb078_alpha_dummy_587 g) ≠ (nb078_alpha_dummy_588 g) := by
  simpa only [nb078_alpha_dummy_587, nb078_alpha_dummy_588] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_580 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_784 : (nb078_alpha_dummy_591) ∉ (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_591] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_785 : (nb078_alpha_dummy_592) ∉ (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_592] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_786 : (nb078_alpha_dummy_593) ∉ (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_593] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_787 : (nb078_alpha_dummy_591) ≠ (nb078_alpha_dummy_592) := by
  simpa only [nb078_alpha_dummy_591, nb078_alpha_dummy_592] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_788 : (nb078_alpha_dummy_591) ≠ (nb078_alpha_dummy_593) := by
  simpa only [nb078_alpha_dummy_591, nb078_alpha_dummy_593] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_789 : (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_593) := by
  simpa only [nb078_alpha_dummy_592, nb078_alpha_dummy_593] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_790 (g : Var) : (nb078_alpha_dummy_594 g) ∉ (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_594] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_791 (g : Var) : (nb078_alpha_dummy_595 g) ∉ (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_595] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_792 (g : Var) : (nb078_alpha_dummy_596 g) ∉ (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_596] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_793 (g : Var) : (nb078_alpha_dummy_594 g) ≠ (nb078_alpha_dummy_595 g) := by
  simpa only [nb078_alpha_dummy_594, nb078_alpha_dummy_595] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_794 (g : Var) : (nb078_alpha_dummy_594 g) ≠ (nb078_alpha_dummy_596 g) := by
  simpa only [nb078_alpha_dummy_594, nb078_alpha_dummy_596] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_795 (g : Var) : (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_596 g) := by
  simpa only [nb078_alpha_dummy_595, nb078_alpha_dummy_596] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_796 : (nb078_alpha_dummy_603) ∉ (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_592))).fv) := by
  simpa only [nb078_alpha_dummy_603] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_592))).fv) 0

theorem nb078_fresh_797 : (nb078_alpha_dummy_599) ∉ (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) := by
  simpa only [nb078_alpha_dummy_599] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) 0

theorem nb078_fresh_798 : (nb078_alpha_dummy_605) ∉ (((Class.cv (nb078_alpha_dummy_593))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) := by
  simpa only [nb078_alpha_dummy_605] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_593))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) 0

theorem nb078_fresh_799 (g : Var) : (nb078_alpha_dummy_604 g) ∉ (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_595 g))).fv) := by
  simpa only [nb078_alpha_dummy_604] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_595 g))).fv) 0

theorem nb078_fresh_800 (g : Var) : (nb078_alpha_dummy_600 g) ∉ (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) := by
  simpa only [nb078_alpha_dummy_600] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) 0

theorem nb078_fresh_801 (g : Var) : (nb078_alpha_dummy_606 g) ∉ (((Class.cv (nb078_alpha_dummy_596 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) := by
  simpa only [nb078_alpha_dummy_606] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_596 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) 0

theorem nb078_fresh_802 : (nb078_alpha_dummy_621) ∉ (((Class.cv (nb078_alpha_dummy_614))).fv) := by
  simpa only [nb078_alpha_dummy_621] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_614))).fv) 0

theorem nb078_fresh_803 : (nb078_alpha_dummy_622) ∉ (((Class.cv (nb078_alpha_dummy_614))).fv) := by
  simpa only [nb078_alpha_dummy_622] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_614))).fv) 1

theorem nb078_distinct_804 : (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_622) := by
  simpa only [nb078_alpha_dummy_621, nb078_alpha_dummy_622] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_614))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_805 (g : Var) : (nb078_alpha_dummy_623 g) ∉ (((Class.cv (nb078_alpha_dummy_616 g))).fv) := by
  simpa only [nb078_alpha_dummy_623] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_616 g))).fv) 0

theorem nb078_fresh_806 (g : Var) : (nb078_alpha_dummy_624 g) ∉ (((Class.cv (nb078_alpha_dummy_616 g))).fv) := by
  simpa only [nb078_alpha_dummy_624] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_616 g))).fv) 1

theorem nb078_distinct_807 (g : Var) : (nb078_alpha_dummy_623 g) ≠ (nb078_alpha_dummy_624 g) := by
  simpa only [nb078_alpha_dummy_623, nb078_alpha_dummy_624] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_616 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_808 : (nb078_alpha_dummy_627) ∉ (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_627] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_809 : (nb078_alpha_dummy_628) ∉ (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_628] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_810 : (nb078_alpha_dummy_629) ∉ (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_629] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_811 : (nb078_alpha_dummy_627) ≠ (nb078_alpha_dummy_628) := by
  simpa only [nb078_alpha_dummy_627, nb078_alpha_dummy_628] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_812 : (nb078_alpha_dummy_627) ≠ (nb078_alpha_dummy_629) := by
  simpa only [nb078_alpha_dummy_627, nb078_alpha_dummy_629] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_813 : (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_629) := by
  simpa only [nb078_alpha_dummy_628, nb078_alpha_dummy_629] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_814 (g : Var) : (nb078_alpha_dummy_630 g) ∉ (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_630] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_815 (g : Var) : (nb078_alpha_dummy_631 g) ∉ (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_631] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_816 (g : Var) : (nb078_alpha_dummy_632 g) ∉ (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_632] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_817 (g : Var) : (nb078_alpha_dummy_630 g) ≠ (nb078_alpha_dummy_631 g) := by
  simpa only [nb078_alpha_dummy_630, nb078_alpha_dummy_631] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_818 (g : Var) : (nb078_alpha_dummy_630 g) ≠ (nb078_alpha_dummy_632 g) := by
  simpa only [nb078_alpha_dummy_630, nb078_alpha_dummy_632] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_819 (g : Var) : (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_632 g) := by
  simpa only [nb078_alpha_dummy_631, nb078_alpha_dummy_632] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_820 : (nb078_alpha_dummy_639) ∉ (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_628))).fv) := by
  simpa only [nb078_alpha_dummy_639] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_628))).fv) 0

theorem nb078_fresh_821 : (nb078_alpha_dummy_635) ∉ (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) := by
  simpa only [nb078_alpha_dummy_635] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) 0

theorem nb078_fresh_822 : (nb078_alpha_dummy_641) ∉ (((Class.cv (nb078_alpha_dummy_629))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) := by
  simpa only [nb078_alpha_dummy_641] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_629))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) 0

theorem nb078_fresh_823 (g : Var) : (nb078_alpha_dummy_640 g) ∉ (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_631 g))).fv) := by
  simpa only [nb078_alpha_dummy_640] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_631 g))).fv) 0

theorem nb078_fresh_824 (g : Var) : (nb078_alpha_dummy_636 g) ∉ (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) := by
  simpa only [nb078_alpha_dummy_636] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) 0

theorem nb078_fresh_825 (g : Var) : (nb078_alpha_dummy_642 g) ∉ (((Class.cv (nb078_alpha_dummy_632 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) := by
  simpa only [nb078_alpha_dummy_642] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_632 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) 0

theorem nb078_fresh_826 : (nb078_alpha_dummy_655) ∉ (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) := by
  simpa only [nb078_alpha_dummy_655] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) 0

theorem nb078_fresh_827 : (nb078_alpha_dummy_656) ∉ (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) := by
  simpa only [nb078_alpha_dummy_656] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) 1

theorem nb078_distinct_828 : (nb078_alpha_dummy_655) ≠ (nb078_alpha_dummy_656) := by
  simpa only [nb078_alpha_dummy_655, nb078_alpha_dummy_656] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_829 : (nb078_alpha_dummy_691) ∉ (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) := by
  simpa only [nb078_alpha_dummy_691] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) 0

theorem nb078_fresh_830 : (nb078_alpha_dummy_692) ∉ (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) := by
  simpa only [nb078_alpha_dummy_692] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) 1

theorem nb078_distinct_831 : (nb078_alpha_dummy_691) ≠ (nb078_alpha_dummy_692) := by
  simpa only [nb078_alpha_dummy_691, nb078_alpha_dummy_692] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_832 (g : Var) : (nb078_alpha_dummy_657 g) ∉ (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) := by
  simpa only [nb078_alpha_dummy_657] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) 0

theorem nb078_fresh_833 (g : Var) : (nb078_alpha_dummy_658 g) ∉ (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) := by
  simpa only [nb078_alpha_dummy_658] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) 1

theorem nb078_distinct_834 (g : Var) : (nb078_alpha_dummy_657 g) ≠ (nb078_alpha_dummy_658 g) := by
  simpa only [nb078_alpha_dummy_657, nb078_alpha_dummy_658] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_835 (g : Var) : (nb078_alpha_dummy_693 g) ∉ (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) := by
  simpa only [nb078_alpha_dummy_693] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) 0

theorem nb078_fresh_836 (g : Var) : (nb078_alpha_dummy_694 g) ∉ (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) := by
  simpa only [nb078_alpha_dummy_694] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) 1

theorem nb078_distinct_837 (g : Var) : (nb078_alpha_dummy_693 g) ≠ (nb078_alpha_dummy_694 g) := by
  simpa only [nb078_alpha_dummy_693, nb078_alpha_dummy_694] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_838 : (nb078_alpha_dummy_663) ∉ (((Class.cv (nb078_alpha_dummy_656))).fv) := by
  simpa only [nb078_alpha_dummy_663] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_656))).fv) 0

theorem nb078_fresh_839 : (nb078_alpha_dummy_664) ∉ (((Class.cv (nb078_alpha_dummy_656))).fv) := by
  simpa only [nb078_alpha_dummy_664] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_656))).fv) 1

theorem nb078_distinct_840 : (nb078_alpha_dummy_663) ≠ (nb078_alpha_dummy_664) := by
  simpa only [nb078_alpha_dummy_663, nb078_alpha_dummy_664] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_656))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_841 (g : Var) : (nb078_alpha_dummy_665 g) ∉ (((Class.cv (nb078_alpha_dummy_658 g))).fv) := by
  simpa only [nb078_alpha_dummy_665] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_658 g))).fv) 0

theorem nb078_fresh_842 (g : Var) : (nb078_alpha_dummy_666 g) ∉ (((Class.cv (nb078_alpha_dummy_658 g))).fv) := by
  simpa only [nb078_alpha_dummy_666] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_658 g))).fv) 1

theorem nb078_distinct_843 (g : Var) : (nb078_alpha_dummy_665 g) ≠ (nb078_alpha_dummy_666 g) := by
  simpa only [nb078_alpha_dummy_665, nb078_alpha_dummy_666] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_658 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_844 : (nb078_alpha_dummy_669) ∉ (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_669] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_845 : (nb078_alpha_dummy_670) ∉ (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_670] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_846 : (nb078_alpha_dummy_671) ∉ (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_671] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_847 : (nb078_alpha_dummy_669) ≠ (nb078_alpha_dummy_670) := by
  simpa only [nb078_alpha_dummy_669, nb078_alpha_dummy_670] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_848 : (nb078_alpha_dummy_669) ≠ (nb078_alpha_dummy_671) := by
  simpa only [nb078_alpha_dummy_669, nb078_alpha_dummy_671] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_849 : (nb078_alpha_dummy_670) ≠ (nb078_alpha_dummy_671) := by
  simpa only [nb078_alpha_dummy_670, nb078_alpha_dummy_671] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_850 (g : Var) : (nb078_alpha_dummy_672 g) ∉ (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_672] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_851 (g : Var) : (nb078_alpha_dummy_673 g) ∉ (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_673] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_852 (g : Var) : (nb078_alpha_dummy_674 g) ∉ (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_674] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_853 (g : Var) : (nb078_alpha_dummy_672 g) ≠ (nb078_alpha_dummy_673 g) := by
  simpa only [nb078_alpha_dummy_672, nb078_alpha_dummy_673] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
