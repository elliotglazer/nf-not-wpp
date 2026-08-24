import NAR4C090C001Part011

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

theorem nb090_distinct_692 (A : Class) : (nb090_alpha_dummy_759 A) ≠ (nb090_alpha_dummy_761 A) := by
  simpa only [nb090_alpha_dummy_759, nb090_alpha_dummy_761] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_693 (A : Class) : (nb090_alpha_dummy_760 A) ≠ (nb090_alpha_dummy_761 A) := by
  simpa only [nb090_alpha_dummy_760, nb090_alpha_dummy_761] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_694 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_762 v u h) ∉ (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_762] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_695 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_763 v u h) ∉ (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_763] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_696 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_764 v u h) ∉ (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_764] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_697 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_762 v u h) ≠ (nb090_alpha_dummy_763 v u h) := by
  simpa only [nb090_alpha_dummy_762, nb090_alpha_dummy_763] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_698 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_762 v u h) ≠ (nb090_alpha_dummy_764 v u h) := by
  simpa only [nb090_alpha_dummy_762, nb090_alpha_dummy_764] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_699 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_764 v u h) := by
  simpa only [nb090_alpha_dummy_763, nb090_alpha_dummy_764] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_700 (A : Class) : (nb090_alpha_dummy_771 A) ∉ (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_760 A))).fv) := by
  simpa only [nb090_alpha_dummy_771] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_760 A))).fv) 0

theorem nb090_fresh_701 (A : Class) : (nb090_alpha_dummy_767 A) ∉ (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) := by
  simpa only [nb090_alpha_dummy_767] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) 0

theorem nb090_fresh_702 (A : Class) : (nb090_alpha_dummy_773 A) ∉ (((Class.cv (nb090_alpha_dummy_761 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) := by
  simpa only [nb090_alpha_dummy_773] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_761 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) 0

theorem nb090_fresh_703 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_772 v u h) ∉ (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_763 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_772] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_763 v u h))).fv) 0

theorem nb090_fresh_704 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_768 v u h) ∉ (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_768] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) 0

theorem nb090_fresh_705 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_774 v u h) ∉ (((Class.cv (nb090_alpha_dummy_764 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_774] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_764 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) 0

theorem nb090_fresh_706 (A : Class) : (nb090_alpha_dummy_821 A) ∉ (((Class.cv (nb090_alpha_dummy_779 A))).fv) := by
  simpa only [nb090_alpha_dummy_821] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_779 A))).fv) 0

theorem nb090_fresh_707 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_822 v u h) ∉ (((Class.cv (nb090_alpha_dummy_780 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_822] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_780 v u h))).fv) 0

theorem nb090_fresh_708 (A : Class) : (nb090_alpha_dummy_793 A) ∉ (((Class.cv (nb090_alpha_dummy_786 A))).fv) := by
  simpa only [nb090_alpha_dummy_793] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_786 A))).fv) 0

theorem nb090_fresh_709 (A : Class) : (nb090_alpha_dummy_794 A) ∉ (((Class.cv (nb090_alpha_dummy_786 A))).fv) := by
  simpa only [nb090_alpha_dummy_794] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_786 A))).fv) 1

theorem nb090_distinct_710 (A : Class) : (nb090_alpha_dummy_793 A) ≠ (nb090_alpha_dummy_794 A) := by
  simpa only [nb090_alpha_dummy_793, nb090_alpha_dummy_794] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_786 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_711 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_795 v u h) ∉ (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_795] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) 0

theorem nb090_fresh_712 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_796 v u h) ∉ (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_796] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) 1

theorem nb090_distinct_713 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_795 v u h) ≠ (nb090_alpha_dummy_796 v u h) := by
  simpa only [nb090_alpha_dummy_795, nb090_alpha_dummy_796] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_714 (A : Class) : (nb090_alpha_dummy_799 A) ∉ (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_799] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_715 (A : Class) : (nb090_alpha_dummy_800 A) ∉ (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_800] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_716 (A : Class) : (nb090_alpha_dummy_801 A) ∉ (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_801] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_717 (A : Class) : (nb090_alpha_dummy_799 A) ≠ (nb090_alpha_dummy_800 A) := by
  simpa only [nb090_alpha_dummy_799, nb090_alpha_dummy_800] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_718 (A : Class) : (nb090_alpha_dummy_799 A) ≠ (nb090_alpha_dummy_801 A) := by
  simpa only [nb090_alpha_dummy_799, nb090_alpha_dummy_801] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_719 (A : Class) : (nb090_alpha_dummy_800 A) ≠ (nb090_alpha_dummy_801 A) := by
  simpa only [nb090_alpha_dummy_800, nb090_alpha_dummy_801] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_720 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_802 v u h) ∉ (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_802] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_721 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_803 v u h) ∉ (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_803] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_722 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_804 v u h) ∉ (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_804] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_723 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_802 v u h) ≠ (nb090_alpha_dummy_803 v u h) := by
  simpa only [nb090_alpha_dummy_802, nb090_alpha_dummy_803] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_724 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_802 v u h) ≠ (nb090_alpha_dummy_804 v u h) := by
  simpa only [nb090_alpha_dummy_802, nb090_alpha_dummy_804] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_725 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_804 v u h) := by
  simpa only [nb090_alpha_dummy_803, nb090_alpha_dummy_804] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_726 (A : Class) : (nb090_alpha_dummy_811 A) ∉ (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_800 A))).fv) := by
  simpa only [nb090_alpha_dummy_811] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_800 A))).fv) 0

theorem nb090_fresh_727 (A : Class) : (nb090_alpha_dummy_807 A) ∉ (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) := by
  simpa only [nb090_alpha_dummy_807] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) 0

theorem nb090_fresh_728 (A : Class) : (nb090_alpha_dummy_813 A) ∉ (((Class.cv (nb090_alpha_dummy_801 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) := by
  simpa only [nb090_alpha_dummy_813] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_801 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) 0

theorem nb090_fresh_729 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_812 v u h) ∉ (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_803 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_812] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_803 v u h))).fv) 0

theorem nb090_fresh_730 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_808 v u h) ∉ (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_808] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) 0

theorem nb090_fresh_731 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_814 v u h) ∉ (((Class.cv (nb090_alpha_dummy_804 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_814] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_804 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) 0

theorem nb090_fresh_732 (A : Class) : (nb090_alpha_dummy_871 A) ∉ (((Class.cv (nb090_alpha_dummy_829 A))).fv) := by
  simpa only [nb090_alpha_dummy_871] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_829 A))).fv) 0

theorem nb090_fresh_733 (v : Var) : (nb090_alpha_dummy_872 v) ∉ (((Class.cv (nb090_alpha_dummy_830 v))).fv) := by
  simpa only [nb090_alpha_dummy_872] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_830 v))).fv) 0

theorem nb090_fresh_734 (A : Class) : (nb090_alpha_dummy_843 A) ∉ (((Class.cv (nb090_alpha_dummy_836 A))).fv) := by
  simpa only [nb090_alpha_dummy_843] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_836 A))).fv) 0

theorem nb090_fresh_735 (A : Class) : (nb090_alpha_dummy_844 A) ∉ (((Class.cv (nb090_alpha_dummy_836 A))).fv) := by
  simpa only [nb090_alpha_dummy_844] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_836 A))).fv) 1

theorem nb090_distinct_736 (A : Class) : (nb090_alpha_dummy_843 A) ≠ (nb090_alpha_dummy_844 A) := by
  simpa only [nb090_alpha_dummy_843, nb090_alpha_dummy_844] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_836 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_737 (v : Var) : (nb090_alpha_dummy_845 v) ∉ (((Class.cv (nb090_alpha_dummy_838 v))).fv) := by
  simpa only [nb090_alpha_dummy_845] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_838 v))).fv) 0

theorem nb090_fresh_738 (v : Var) : (nb090_alpha_dummy_846 v) ∉ (((Class.cv (nb090_alpha_dummy_838 v))).fv) := by
  simpa only [nb090_alpha_dummy_846] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_838 v))).fv) 1

theorem nb090_distinct_739 (v : Var) : (nb090_alpha_dummy_845 v) ≠ (nb090_alpha_dummy_846 v) := by
  simpa only [nb090_alpha_dummy_845, nb090_alpha_dummy_846] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_838 v))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_740 (A : Class) : (nb090_alpha_dummy_849 A) ∉ (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_849] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_741 (A : Class) : (nb090_alpha_dummy_850 A) ∉ (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_850] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_742 (A : Class) : (nb090_alpha_dummy_851 A) ∉ (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_851] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_743 (A : Class) : (nb090_alpha_dummy_849 A) ≠ (nb090_alpha_dummy_850 A) := by
  simpa only [nb090_alpha_dummy_849, nb090_alpha_dummy_850] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_744 (A : Class) : (nb090_alpha_dummy_849 A) ≠ (nb090_alpha_dummy_851 A) := by
  simpa only [nb090_alpha_dummy_849, nb090_alpha_dummy_851] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_745 (A : Class) : (nb090_alpha_dummy_850 A) ≠ (nb090_alpha_dummy_851 A) := by
  simpa only [nb090_alpha_dummy_850, nb090_alpha_dummy_851] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_746 (v : Var) : (nb090_alpha_dummy_852 v) ∉ (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_852] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_747 (v : Var) : (nb090_alpha_dummy_853 v) ∉ (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_853] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_748 (v : Var) : (nb090_alpha_dummy_854 v) ∉ (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_854] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_749 (v : Var) : (nb090_alpha_dummy_852 v) ≠ (nb090_alpha_dummy_853 v) := by
  simpa only [nb090_alpha_dummy_852, nb090_alpha_dummy_853] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_750 (v : Var) : (nb090_alpha_dummy_852 v) ≠ (nb090_alpha_dummy_854 v) := by
  simpa only [nb090_alpha_dummy_852, nb090_alpha_dummy_854] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_751 (v : Var) : (nb090_alpha_dummy_853 v) ≠ (nb090_alpha_dummy_854 v) := by
  simpa only [nb090_alpha_dummy_853, nb090_alpha_dummy_854] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_752 (A : Class) : (nb090_alpha_dummy_861 A) ∉ (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_850 A))).fv) := by
  simpa only [nb090_alpha_dummy_861] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_850 A))).fv) 0

theorem nb090_fresh_753 (A : Class) : (nb090_alpha_dummy_857 A) ∉ (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) := by
  simpa only [nb090_alpha_dummy_857] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) 0

theorem nb090_fresh_754 (A : Class) : (nb090_alpha_dummy_863 A) ∉ (((Class.cv (nb090_alpha_dummy_851 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) := by
  simpa only [nb090_alpha_dummy_863] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_851 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) 0

theorem nb090_fresh_755 (v : Var) : (nb090_alpha_dummy_862 v) ∉ (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_853 v))).fv) := by
  simpa only [nb090_alpha_dummy_862] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_853 v))).fv) 0

theorem nb090_fresh_756 (v : Var) : (nb090_alpha_dummy_858 v) ∉ (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) := by
  simpa only [nb090_alpha_dummy_858] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) 0

theorem nb090_fresh_757 (v : Var) : (nb090_alpha_dummy_864 v) ∉ (((Class.cv (nb090_alpha_dummy_854 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) := by
  simpa only [nb090_alpha_dummy_864] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_854 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) 0

theorem nb090_fresh_758 (h : Var) : (nb090_alpha_dummy_131 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb090_alpha_dummy_131] using freshVar_not_mem (((Class.cv h)).fv) 0

theorem nb090_fresh_759 (h : Var) : (nb090_alpha_dummy_132 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb090_alpha_dummy_132] using freshVar_not_mem (((Class.cv h)).fv) 1

theorem nb090_distinct_760 (h : Var) : (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_132 h) := by
  simpa only [nb090_alpha_dummy_131, nb090_alpha_dummy_132] using
    (freshVar_injective (((Class.cv h)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_761 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_708 v u h) ∉ (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_043 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_708] using freshVar_not_mem (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_043 v u h))).fv) 0

theorem nb090_fresh_762 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_778 v u h) ∉ (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_778] using freshVar_not_mem (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) 0

theorem nb090_fresh_763 (h : Var) : (nb090_alpha_dummy_052 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb090_alpha_dummy_052] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 0

theorem nb090_fresh_764 (h : Var) : (nb090_alpha_dummy_053 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb090_alpha_dummy_053] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 1

theorem nb090_fresh_765 (h : Var) : (nb090_alpha_dummy_054 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb090_alpha_dummy_054] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 2

theorem nb090_distinct_766 (h : Var) : (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_053 h) := by
  simpa only [nb090_alpha_dummy_052, nb090_alpha_dummy_053] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_767 (h : Var) : (nb090_alpha_dummy_052 h) ≠ (nb090_alpha_dummy_054 h) := by
  simpa only [nb090_alpha_dummy_052, nb090_alpha_dummy_054] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_768 (h : Var) : (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_054 h) := by
  simpa only [nb090_alpha_dummy_053, nb090_alpha_dummy_054] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_769 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∉ (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) := by
  simpa only [nb090_alpha_dummy_043] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) 0

theorem nb090_fresh_770 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∉ (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) := by
  simpa only [nb090_alpha_dummy_044] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) 1

theorem nb090_distinct_771 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_044 v u h) := by
  simpa only [nb090_alpha_dummy_043, nb090_alpha_dummy_044] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_772 (h : Var) : (nb090_alpha_dummy_335 h) ∉ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb090_alpha_dummy_335] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 0

theorem nb090_fresh_773 (h : Var) : (nb090_alpha_dummy_336 h) ∉ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb090_alpha_dummy_336] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 1

theorem nb090_distinct_774 (h : Var) : (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_336 h) := by
  simpa only [nb090_alpha_dummy_335, nb090_alpha_dummy_336] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_775 (u : Var) : (nb090_alpha_dummy_293 u) ∉ (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) := by
  simpa only [nb090_alpha_dummy_293] using freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) 0

theorem nb090_fresh_776 (u : Var) : (nb090_alpha_dummy_294 u) ∉ (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) := by
  simpa only [nb090_alpha_dummy_294] using freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) 1

theorem nb090_distinct_777 (u : Var) : (nb090_alpha_dummy_293 u) ≠ (nb090_alpha_dummy_294 u) := by
  simpa only [nb090_alpha_dummy_293, nb090_alpha_dummy_294] using
    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_778 (u : Var) : (nb090_alpha_dummy_663 u) ∉ (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) := by
  simpa only [nb090_alpha_dummy_663] using freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) 0

theorem nb090_fresh_779 (u : Var) : (nb090_alpha_dummy_664 u) ∉ (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) := by
  simpa only [nb090_alpha_dummy_664] using freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) 1

theorem nb090_distinct_780 (u : Var) : (nb090_alpha_dummy_663 u) ≠ (nb090_alpha_dummy_664 u) := by
  simpa only [nb090_alpha_dummy_663, nb090_alpha_dummy_664] using
    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_781 (v : Var) (u : Var) : (nb090_alpha_dummy_007 v u) ∉ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090_alpha_dummy_007] using freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 0

theorem nb090_fresh_782 (v : Var) (u : Var) : (nb090_alpha_dummy_008 v u) ∉ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090_alpha_dummy_008] using freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 1

theorem nb090_distinct_783 (v : Var) (u : Var) : (nb090_alpha_dummy_007 v u) ≠ (nb090_alpha_dummy_008 v u) := by
  simpa only [nb090_alpha_dummy_007, nb090_alpha_dummy_008] using
    (freshVar_injective (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_784 (v : Var) : (nb090_alpha_dummy_383 v) ∉ (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) := by
  simpa only [nb090_alpha_dummy_383] using freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) 0

theorem nb090_fresh_785 (v : Var) : (nb090_alpha_dummy_384 v) ∉ (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) := by
  simpa only [nb090_alpha_dummy_384] using freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) 1

theorem nb090_distinct_786 (v : Var) : (nb090_alpha_dummy_383 v) ≠ (nb090_alpha_dummy_384 v) := by
  simpa only [nb090_alpha_dummy_383, nb090_alpha_dummy_384] using
    (freshVar_injective (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_787 (v : Var) : (nb090_alpha_dummy_837 v) ∉ (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) := by
  simpa only [nb090_alpha_dummy_837] using freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) 0

theorem nb090_fresh_788 (v : Var) : (nb090_alpha_dummy_838 v) ∉ (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) := by
  simpa only [nb090_alpha_dummy_838] using freshVar_not_mem (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) 1

theorem nb090_distinct_789 (v : Var) : (nb090_alpha_dummy_837 v) ≠ (nb090_alpha_dummy_838 v) := by
  simpa only [nb090_alpha_dummy_837, nb090_alpha_dummy_838] using
    (freshVar_injective (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_790 (A : Class) : (nb090_alpha_dummy_017 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_013 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_013 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_013 A))).fv) := by
  simpa only [nb090_alpha_dummy_017] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_013 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_013 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_013 A))).fv) 0

theorem nb090_fresh_791 (v : Var) (u : Var) : (nb090_alpha_dummy_018 v u) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_015 v u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_015 v u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_015 v u))).fv) := by
  simpa only [nb090_alpha_dummy_018] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_015 v u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_015 v u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_015 v u))).fv) 0

theorem nb090_fresh_792 (A : Class) : (nb090_alpha_dummy_069 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_065 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_065 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_065 A))).fv) := by
  simpa only [nb090_alpha_dummy_069] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_065 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_065 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_065 A))).fv) 0

theorem nb090_fresh_793 (h : Var) : (nb090_alpha_dummy_070 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_067 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_067 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_067 h))).fv) := by
  simpa only [nb090_alpha_dummy_070] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_067 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_067 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_067 h))).fv) 0

theorem nb090_fresh_794 (A : Class) : (nb090_alpha_dummy_105 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_101 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_101 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_101 A))).fv) := by
  simpa only [nb090_alpha_dummy_105] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_101 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_101 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_101 A))).fv) 0

theorem nb090_fresh_795 (h : Var) : (nb090_alpha_dummy_106 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_103 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_103 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_103 h))).fv) := by
  simpa only [nb090_alpha_dummy_106] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_103 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_103 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_103 h))).fv) 0

theorem nb090_fresh_796 (A : Class) : (nb090_alpha_dummy_147 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_143 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_143 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_143 A))).fv) := by
  simpa only [nb090_alpha_dummy_147] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_143 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_143 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_143 A))).fv) 0

theorem nb090_fresh_797 (h : Var) : (nb090_alpha_dummy_148 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_145 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_145 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_145 h))).fv) := by
  simpa only [nb090_alpha_dummy_148] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_145 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_145 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_145 h))).fv) 0

theorem nb090_fresh_798 (A : Class) : (nb090_alpha_dummy_183 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_179 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_179 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_179 A))).fv) := by
  simpa only [nb090_alpha_dummy_183] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_179 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_179 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_179 A))).fv) 0

theorem nb090_fresh_799 (h : Var) : (nb090_alpha_dummy_184 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_181 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_181 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_181 h))).fv) := by
  simpa only [nb090_alpha_dummy_184] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_181 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_181 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_181 h))).fv) 0

theorem nb090_fresh_800 (A : Class) : (nb090_alpha_dummy_219 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_215 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_215 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_215 A))).fv) := by
  simpa only [nb090_alpha_dummy_219] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_215 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_215 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_215 A))).fv) 0

theorem nb090_fresh_801 (h : Var) : (nb090_alpha_dummy_220 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_217 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_217 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_217 h))).fv) := by
  simpa only [nb090_alpha_dummy_220] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_217 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_217 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_217 h))).fv) 0

theorem nb090_fresh_802 (A : Class) : (nb090_alpha_dummy_259 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_255 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_255 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_255 A))).fv) := by
  simpa only [nb090_alpha_dummy_259] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_255 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_255 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_255 A))).fv) 0

theorem nb090_fresh_803 (h : Var) : (nb090_alpha_dummy_260 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_257 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_257 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_257 h))).fv) := by
  simpa only [nb090_alpha_dummy_260] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_257 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_257 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_257 h))).fv) 0

theorem nb090_fresh_804 (A : Class) : (nb090_alpha_dummy_303 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_299 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_299 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_299 A))).fv) := by
  simpa only [nb090_alpha_dummy_303] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_299 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_299 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_299 A))).fv) 0

theorem nb090_fresh_805 (u : Var) : (nb090_alpha_dummy_304 u) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_301 u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_301 u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_301 u))).fv) := by
  simpa only [nb090_alpha_dummy_304] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_301 u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_301 u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_301 u))).fv) 0

theorem nb090_fresh_806 (A : Class) : (nb090_alpha_dummy_349 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_345 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_345 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_345 A))).fv) := by
  simpa only [nb090_alpha_dummy_349] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_345 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_345 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_345 A))).fv) 0

theorem nb090_fresh_807 (h : Var) : (nb090_alpha_dummy_350 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_347 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_347 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_347 h))).fv) := by
  simpa only [nb090_alpha_dummy_350] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_347 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_347 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_347 h))).fv) 0

theorem nb090_fresh_808 (A : Class) : (nb090_alpha_dummy_393 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_389 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_389 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_389 A))).fv) := by
  simpa only [nb090_alpha_dummy_393] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_389 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_389 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_389 A))).fv) 0

theorem nb090_fresh_809 (v : Var) : (nb090_alpha_dummy_394 v) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_391 v)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_391 v)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_391 v))).fv) := by
  simpa only [nb090_alpha_dummy_394] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_391 v)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_391 v)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_391 v))).fv) 0

theorem nb090_fresh_810 (A : Class) : (nb090_alpha_dummy_443 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_439 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_439 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_439 A))).fv) := by
  simpa only [nb090_alpha_dummy_443] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_439 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_439 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_439 A))).fv) 0

theorem nb090_fresh_811 (h : Var) : (nb090_alpha_dummy_444 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_441 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_441 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_441 h))).fv) := by
  simpa only [nb090_alpha_dummy_444] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_441 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_441 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_441 h))).fv) 0

theorem nb090_fresh_812 (A : Class) : (nb090_alpha_dummy_479 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_475 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_475 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_475 A))).fv) := by
  simpa only [nb090_alpha_dummy_479] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_475 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_475 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_475 A))).fv) 0

theorem nb090_fresh_813 (h : Var) : (nb090_alpha_dummy_480 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_477 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_477 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_477 h))).fv) := by
  simpa only [nb090_alpha_dummy_480] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_477 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_477 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_477 h))).fv) 0

theorem nb090_fresh_814 (A : Class) : (nb090_alpha_dummy_521 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_517 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_517 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_517 A))).fv) := by
  simpa only [nb090_alpha_dummy_521] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_517 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_517 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_517 A))).fv) 0

theorem nb090_fresh_815 (h : Var) : (nb090_alpha_dummy_522 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_519 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_519 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_519 h))).fv) := by
  simpa only [nb090_alpha_dummy_522] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_519 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_519 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_519 h))).fv) 0

theorem nb090_fresh_816 (A : Class) : (nb090_alpha_dummy_557 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_553 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_553 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_553 A))).fv) := by
  simpa only [nb090_alpha_dummy_557] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_553 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_553 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_553 A))).fv) 0

theorem nb090_fresh_817 (h : Var) : (nb090_alpha_dummy_558 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_555 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_555 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_555 h))).fv) := by
  simpa only [nb090_alpha_dummy_558] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_555 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_555 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_555 h))).fv) 0

theorem nb090_fresh_818 (A : Class) : (nb090_alpha_dummy_593 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_589 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_589 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_589 A))).fv) := by
  simpa only [nb090_alpha_dummy_593] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_589 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_589 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_589 A))).fv) 0

theorem nb090_fresh_819 (h : Var) : (nb090_alpha_dummy_594 h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_591 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_591 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_591 h))).fv) := by
  simpa only [nb090_alpha_dummy_594] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_591 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_591 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_591 h))).fv) 0

theorem nb090_fresh_820 (A : Class) : (nb090_alpha_dummy_629 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_625 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_625 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_625 A))).fv) := by
  simpa only [nb090_alpha_dummy_629] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_625 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_625 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_625 A))).fv) 0

theorem nb090_fresh_821 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_630 v u h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_627 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_630] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_627 v u h))).fv) 0

theorem nb090_fresh_822 (A : Class) : (nb090_alpha_dummy_673 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_669 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_669 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_669 A))).fv) := by
  simpa only [nb090_alpha_dummy_673] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_669 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_669 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_669 A))).fv) 0

theorem nb090_fresh_823 (u : Var) : (nb090_alpha_dummy_674 u) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_671 u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_671 u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_671 u))).fv) := by
  simpa only [nb090_alpha_dummy_674] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_671 u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_671 u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_671 u))).fv) 0

theorem nb090_fresh_824 (A : Class) : (nb090_alpha_dummy_727 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_723 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_723 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_723 A))).fv) := by
  simpa only [nb090_alpha_dummy_727] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_723 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_723 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_723 A))).fv) 0

theorem nb090_fresh_825 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_728 v u h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_725 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_728] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_725 v u h))).fv) 0

theorem nb090_fresh_826 (A : Class) : (nb090_alpha_dummy_757 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_753 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_753 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_753 A))).fv) := by
  simpa only [nb090_alpha_dummy_757] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_753 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_753 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_753 A))).fv) 0

theorem nb090_fresh_827 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_758 v u h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_755 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_758] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_755 v u h))).fv) 0

theorem nb090_fresh_828 (A : Class) : (nb090_alpha_dummy_797 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_793 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_793 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_793 A))).fv) := by
  simpa only [nb090_alpha_dummy_797] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_793 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_793 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_793 A))).fv) 0

theorem nb090_fresh_829 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_798 v u h) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_795 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_798] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_795 v u h))).fv) 0

theorem nb090_fresh_830 (A : Class) : (nb090_alpha_dummy_847 A) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_843 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_843 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_843 A))).fv) := by
  simpa only [nb090_alpha_dummy_847] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_843 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_843 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_843 A))).fv) 0

theorem nb090_fresh_831 (v : Var) : (nb090_alpha_dummy_848 v) ∉ (((Wff.classMem (Class.cv (nb090_alpha_dummy_845 v)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_845 v)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_845 v))).fv) := by
  simpa only [nb090_alpha_dummy_848] using freshVar_not_mem (((Wff.classMem (Class.cv (nb090_alpha_dummy_845 v)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_845 v)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_845 v))).fv) 0

theorem nb090_fresh_832 (A : Class) : (nb090_alpha_dummy_653 A) ∉ (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) := by
  simpa only [nb090_alpha_dummy_653] using freshVar_not_mem (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) 0

theorem nb090_fresh_833 (A : Class) : (nb090_alpha_dummy_827 A) ∉ (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) := by
  simpa only [nb090_alpha_dummy_827] using freshVar_not_mem (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0

theorem nb090_fresh_834 (u : Var) : (nb090_alpha_dummy_654 u) ∉ (((syn_c1st)).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb090_alpha_dummy_654] using freshVar_not_mem (((syn_c1st)).fv ∪ ((Class.cv u)).fv) 0

theorem nb090_fresh_835 (v : Var) : (nb090_alpha_dummy_828 v) ∉ (((syn_c1st)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090_alpha_dummy_828] using freshVar_not_mem (((syn_c1st)).fv ∪ ((Class.cv v)).fv) 0

theorem nb090_fresh_836 (A : Class) : (nb090_alpha_dummy_283 A) ∉ (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) := by
  simpa only [nb090_alpha_dummy_283] using freshVar_not_mem (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) 0

theorem nb090_fresh_837 (A : Class) : (nb090_alpha_dummy_373 A) ∉ (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) := by
  simpa only [nb090_alpha_dummy_373] using freshVar_not_mem (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0

theorem nb090_fresh_838 (u : Var) : (nb090_alpha_dummy_284 u) ∉ (((syn_c2nd)).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb090_alpha_dummy_284] using freshVar_not_mem (((syn_c2nd)).fv ∪ ((Class.cv u)).fv) 0

theorem nb090_fresh_839 (v : Var) : (nb090_alpha_dummy_374 v) ∉ (((syn_c2nd)).fv ∪ ((Class.cv v)).fv) := by
  simpa only [nb090_alpha_dummy_374] using freshVar_not_mem (((syn_c2nd)).fv ∪ ((Class.cv v)).fv) 0

theorem nb090_fresh_840 (A : Class) : (nb090_alpha_dummy_503 A) ∉ (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) := by
  simpa only [nb090_alpha_dummy_503] using freshVar_not_mem (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 0

theorem nb090_fresh_841 (A : Class) : (nb090_alpha_dummy_504 A) ∉ (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) := by
  simpa only [nb090_alpha_dummy_504] using freshVar_not_mem (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
