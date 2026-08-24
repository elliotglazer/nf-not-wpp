import NAR4C078C001Part015

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

theorem nb078_distinct_854 (g : Var) : (nb078_alpha_dummy_672 g) ≠ (nb078_alpha_dummy_674 g) := by
  simpa only [nb078_alpha_dummy_672, nb078_alpha_dummy_674] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_855 (g : Var) : (nb078_alpha_dummy_673 g) ≠ (nb078_alpha_dummy_674 g) := by
  simpa only [nb078_alpha_dummy_673, nb078_alpha_dummy_674] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_856 : (nb078_alpha_dummy_681) ∉ (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_670))).fv) := by
  simpa only [nb078_alpha_dummy_681] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_670))).fv) 0

theorem nb078_fresh_857 : (nb078_alpha_dummy_677) ∉ (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) := by
  simpa only [nb078_alpha_dummy_677] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) 0

theorem nb078_fresh_858 : (nb078_alpha_dummy_683) ∉ (((Class.cv (nb078_alpha_dummy_671))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) := by
  simpa only [nb078_alpha_dummy_683] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_671))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) 0

theorem nb078_fresh_859 (g : Var) : (nb078_alpha_dummy_682 g) ∉ (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_673 g))).fv) := by
  simpa only [nb078_alpha_dummy_682] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_673 g))).fv) 0

theorem nb078_fresh_860 (g : Var) : (nb078_alpha_dummy_678 g) ∉ (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) := by
  simpa only [nb078_alpha_dummy_678] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) 0

theorem nb078_fresh_861 (g : Var) : (nb078_alpha_dummy_684 g) ∉ (((Class.cv (nb078_alpha_dummy_674 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) := by
  simpa only [nb078_alpha_dummy_684] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_674 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) 0

theorem nb078_fresh_862 : (nb078_alpha_dummy_699) ∉ (((Class.cv (nb078_alpha_dummy_692))).fv) := by
  simpa only [nb078_alpha_dummy_699] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_692))).fv) 0

theorem nb078_fresh_863 : (nb078_alpha_dummy_700) ∉ (((Class.cv (nb078_alpha_dummy_692))).fv) := by
  simpa only [nb078_alpha_dummy_700] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_692))).fv) 1

theorem nb078_distinct_864 : (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_700) := by
  simpa only [nb078_alpha_dummy_699, nb078_alpha_dummy_700] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_692))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_865 (g : Var) : (nb078_alpha_dummy_701 g) ∉ (((Class.cv (nb078_alpha_dummy_694 g))).fv) := by
  simpa only [nb078_alpha_dummy_701] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_694 g))).fv) 0

theorem nb078_fresh_866 (g : Var) : (nb078_alpha_dummy_702 g) ∉ (((Class.cv (nb078_alpha_dummy_694 g))).fv) := by
  simpa only [nb078_alpha_dummy_702] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_694 g))).fv) 1

theorem nb078_distinct_867 (g : Var) : (nb078_alpha_dummy_701 g) ≠ (nb078_alpha_dummy_702 g) := by
  simpa only [nb078_alpha_dummy_701, nb078_alpha_dummy_702] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_694 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_868 : (nb078_alpha_dummy_705) ∉ (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_705] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_869 : (nb078_alpha_dummy_706) ∉ (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_706] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_870 : (nb078_alpha_dummy_707) ∉ (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_707] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_871 : (nb078_alpha_dummy_705) ≠ (nb078_alpha_dummy_706) := by
  simpa only [nb078_alpha_dummy_705, nb078_alpha_dummy_706] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_872 : (nb078_alpha_dummy_705) ≠ (nb078_alpha_dummy_707) := by
  simpa only [nb078_alpha_dummy_705, nb078_alpha_dummy_707] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_873 : (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_707) := by
  simpa only [nb078_alpha_dummy_706, nb078_alpha_dummy_707] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_874 (g : Var) : (nb078_alpha_dummy_708 g) ∉ (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_708] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_875 (g : Var) : (nb078_alpha_dummy_709 g) ∉ (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_709] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_876 (g : Var) : (nb078_alpha_dummy_710 g) ∉ (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_710] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_877 (g : Var) : (nb078_alpha_dummy_708 g) ≠ (nb078_alpha_dummy_709 g) := by
  simpa only [nb078_alpha_dummy_708, nb078_alpha_dummy_709] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_878 (g : Var) : (nb078_alpha_dummy_708 g) ≠ (nb078_alpha_dummy_710 g) := by
  simpa only [nb078_alpha_dummy_708, nb078_alpha_dummy_710] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_879 (g : Var) : (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_710 g) := by
  simpa only [nb078_alpha_dummy_709, nb078_alpha_dummy_710] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_880 : (nb078_alpha_dummy_717) ∉ (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_706))).fv) := by
  simpa only [nb078_alpha_dummy_717] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_706))).fv) 0

theorem nb078_fresh_881 : (nb078_alpha_dummy_713) ∉ (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) := by
  simpa only [nb078_alpha_dummy_713] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) 0

theorem nb078_fresh_882 : (nb078_alpha_dummy_719) ∉ (((Class.cv (nb078_alpha_dummy_707))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) := by
  simpa only [nb078_alpha_dummy_719] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_707))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) 0

theorem nb078_fresh_883 (g : Var) : (nb078_alpha_dummy_718 g) ∉ (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_709 g))).fv) := by
  simpa only [nb078_alpha_dummy_718] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_709 g))).fv) 0

theorem nb078_fresh_884 (g : Var) : (nb078_alpha_dummy_714 g) ∉ (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) := by
  simpa only [nb078_alpha_dummy_714] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) 0

theorem nb078_fresh_885 (g : Var) : (nb078_alpha_dummy_720 g) ∉ (((Class.cv (nb078_alpha_dummy_710 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) := by
  simpa only [nb078_alpha_dummy_720] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_710 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) 0

theorem nb078_fresh_886 : (nb078_alpha_dummy_735) ∉ (((Class.cv (nb078_alpha_dummy_728))).fv) := by
  simpa only [nb078_alpha_dummy_735] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_728))).fv) 0

theorem nb078_fresh_887 : (nb078_alpha_dummy_736) ∉ (((Class.cv (nb078_alpha_dummy_728))).fv) := by
  simpa only [nb078_alpha_dummy_736] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_728))).fv) 1

theorem nb078_distinct_888 : (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_736) := by
  simpa only [nb078_alpha_dummy_735, nb078_alpha_dummy_736] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_728))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_889 (g : Var) : (nb078_alpha_dummy_737 g) ∉ (((Class.cv (nb078_alpha_dummy_730 g))).fv) := by
  simpa only [nb078_alpha_dummy_737] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_730 g))).fv) 0

theorem nb078_fresh_890 (g : Var) : (nb078_alpha_dummy_738 g) ∉ (((Class.cv (nb078_alpha_dummy_730 g))).fv) := by
  simpa only [nb078_alpha_dummy_738] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_730 g))).fv) 1

theorem nb078_distinct_891 (g : Var) : (nb078_alpha_dummy_737 g) ≠ (nb078_alpha_dummy_738 g) := by
  simpa only [nb078_alpha_dummy_737, nb078_alpha_dummy_738] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_730 g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_892 : (nb078_alpha_dummy_741) ∉ (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_741] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_893 : (nb078_alpha_dummy_742) ∉ (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_742] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_894 : (nb078_alpha_dummy_743) ∉ (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_743] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_895 : (nb078_alpha_dummy_741) ≠ (nb078_alpha_dummy_742) := by
  simpa only [nb078_alpha_dummy_741, nb078_alpha_dummy_742] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_896 : (nb078_alpha_dummy_741) ≠ (nb078_alpha_dummy_743) := by
  simpa only [nb078_alpha_dummy_741, nb078_alpha_dummy_743] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_897 : (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_743) := by
  simpa only [nb078_alpha_dummy_742, nb078_alpha_dummy_743] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_898 (g : Var) : (nb078_alpha_dummy_744 g) ∉ (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_744] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_899 (g : Var) : (nb078_alpha_dummy_745 g) ∉ (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_745] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_900 (g : Var) : (nb078_alpha_dummy_746 g) ∉ (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_746] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_901 (g : Var) : (nb078_alpha_dummy_744 g) ≠ (nb078_alpha_dummy_745 g) := by
  simpa only [nb078_alpha_dummy_744, nb078_alpha_dummy_745] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_902 (g : Var) : (nb078_alpha_dummy_744 g) ≠ (nb078_alpha_dummy_746 g) := by
  simpa only [nb078_alpha_dummy_744, nb078_alpha_dummy_746] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_903 (g : Var) : (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_746 g) := by
  simpa only [nb078_alpha_dummy_745, nb078_alpha_dummy_746] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_904 : (nb078_alpha_dummy_753) ∉ (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_742))).fv) := by
  simpa only [nb078_alpha_dummy_753] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_742))).fv) 0

theorem nb078_fresh_905 : (nb078_alpha_dummy_749) ∉ (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) := by
  simpa only [nb078_alpha_dummy_749] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) 0

theorem nb078_fresh_906 : (nb078_alpha_dummy_755) ∉ (((Class.cv (nb078_alpha_dummy_743))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) := by
  simpa only [nb078_alpha_dummy_755] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_743))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) 0

theorem nb078_fresh_907 (g : Var) : (nb078_alpha_dummy_754 g) ∉ (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_745 g))).fv) := by
  simpa only [nb078_alpha_dummy_754] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_745 g))).fv) 0

theorem nb078_fresh_908 (g : Var) : (nb078_alpha_dummy_750 g) ∉ (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) := by
  simpa only [nb078_alpha_dummy_750] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) 0

theorem nb078_fresh_909 (g : Var) : (nb078_alpha_dummy_756 g) ∉ (((Class.cv (nb078_alpha_dummy_746 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) := by
  simpa only [nb078_alpha_dummy_756] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_746 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) 0

theorem nb078_fresh_910 : (nb078_alpha_dummy_775) ∉ (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) := by
  simpa only [nb078_alpha_dummy_775] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 0

theorem nb078_fresh_911 : (nb078_alpha_dummy_776) ∉ (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) := by
  simpa only [nb078_alpha_dummy_776] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 1

theorem nb078_distinct_912 : (nb078_alpha_dummy_775) ≠ (nb078_alpha_dummy_776) := by
  simpa only [nb078_alpha_dummy_775, nb078_alpha_dummy_776] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_913 : (nb078_alpha_dummy_811) ∉ (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) := by
  simpa only [nb078_alpha_dummy_811] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) 0

theorem nb078_fresh_914 : (nb078_alpha_dummy_812) ∉ (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) := by
  simpa only [nb078_alpha_dummy_812] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) 1

theorem nb078_distinct_915 : (nb078_alpha_dummy_811) ≠ (nb078_alpha_dummy_812) := by
  simpa only [nb078_alpha_dummy_811, nb078_alpha_dummy_812] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_916 : (nb078_alpha_dummy_925) ∉ (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) := by
  simpa only [nb078_alpha_dummy_925] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 0

theorem nb078_fresh_917 : (nb078_alpha_dummy_926) ∉ (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) := by
  simpa only [nb078_alpha_dummy_926] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 1

theorem nb078_distinct_918 : (nb078_alpha_dummy_925) ≠ (nb078_alpha_dummy_926) := by
  simpa only [nb078_alpha_dummy_925, nb078_alpha_dummy_926] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_919 (h : Var) : (nb078_alpha_dummy_777 h) ∉ (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) := by
  simpa only [nb078_alpha_dummy_777] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) 0

theorem nb078_fresh_920 (h : Var) : (nb078_alpha_dummy_778 h) ∉ (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) := by
  simpa only [nb078_alpha_dummy_778] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) 1

theorem nb078_distinct_921 (h : Var) : (nb078_alpha_dummy_777 h) ≠ (nb078_alpha_dummy_778 h) := by
  simpa only [nb078_alpha_dummy_777, nb078_alpha_dummy_778] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_922 (h : Var) : (nb078_alpha_dummy_813 h) ∉ (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) := by
  simpa only [nb078_alpha_dummy_813] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) 0

theorem nb078_fresh_923 (h : Var) : (nb078_alpha_dummy_814 h) ∉ (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) := by
  simpa only [nb078_alpha_dummy_814] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) 1

theorem nb078_distinct_924 (h : Var) : (nb078_alpha_dummy_813 h) ≠ (nb078_alpha_dummy_814 h) := by
  simpa only [nb078_alpha_dummy_813, nb078_alpha_dummy_814] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_925 (h : Var) : (nb078_alpha_dummy_927 h) ∉ (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) := by
  simpa only [nb078_alpha_dummy_927] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) 0

theorem nb078_fresh_926 (h : Var) : (nb078_alpha_dummy_928 h) ∉ (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) := by
  simpa only [nb078_alpha_dummy_928] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) 1

theorem nb078_distinct_927 (h : Var) : (nb078_alpha_dummy_927 h) ≠ (nb078_alpha_dummy_928 h) := by
  simpa only [nb078_alpha_dummy_927, nb078_alpha_dummy_928] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_928 : (nb078_alpha_dummy_783) ∉ (((Class.cv (nb078_alpha_dummy_776))).fv) := by
  simpa only [nb078_alpha_dummy_783] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_776))).fv) 0

theorem nb078_fresh_929 : (nb078_alpha_dummy_784) ∉ (((Class.cv (nb078_alpha_dummy_776))).fv) := by
  simpa only [nb078_alpha_dummy_784] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_776))).fv) 1

theorem nb078_distinct_930 : (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_784) := by
  simpa only [nb078_alpha_dummy_783, nb078_alpha_dummy_784] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_776))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_931 (h : Var) : (nb078_alpha_dummy_785 h) ∉ (((Class.cv (nb078_alpha_dummy_778 h))).fv) := by
  simpa only [nb078_alpha_dummy_785] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_778 h))).fv) 0

theorem nb078_fresh_932 (h : Var) : (nb078_alpha_dummy_786 h) ∉ (((Class.cv (nb078_alpha_dummy_778 h))).fv) := by
  simpa only [nb078_alpha_dummy_786] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_778 h))).fv) 1

theorem nb078_distinct_933 (h : Var) : (nb078_alpha_dummy_785 h) ≠ (nb078_alpha_dummy_786 h) := by
  simpa only [nb078_alpha_dummy_785, nb078_alpha_dummy_786] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_778 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_934 : (nb078_alpha_dummy_789) ∉ (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_789] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_935 : (nb078_alpha_dummy_790) ∉ (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_790] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_936 : (nb078_alpha_dummy_791) ∉ (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_791] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_937 : (nb078_alpha_dummy_789) ≠ (nb078_alpha_dummy_790) := by
  simpa only [nb078_alpha_dummy_789, nb078_alpha_dummy_790] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_938 : (nb078_alpha_dummy_789) ≠ (nb078_alpha_dummy_791) := by
  simpa only [nb078_alpha_dummy_789, nb078_alpha_dummy_791] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_939 : (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_791) := by
  simpa only [nb078_alpha_dummy_790, nb078_alpha_dummy_791] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_940 (h : Var) : (nb078_alpha_dummy_792 h) ∉ (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_792] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_941 (h : Var) : (nb078_alpha_dummy_793 h) ∉ (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_793] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_942 (h : Var) : (nb078_alpha_dummy_794 h) ∉ (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_794] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_943 (h : Var) : (nb078_alpha_dummy_792 h) ≠ (nb078_alpha_dummy_793 h) := by
  simpa only [nb078_alpha_dummy_792, nb078_alpha_dummy_793] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_944 (h : Var) : (nb078_alpha_dummy_792 h) ≠ (nb078_alpha_dummy_794 h) := by
  simpa only [nb078_alpha_dummy_792, nb078_alpha_dummy_794] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_945 (h : Var) : (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_794 h) := by
  simpa only [nb078_alpha_dummy_793, nb078_alpha_dummy_794] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_946 : (nb078_alpha_dummy_801) ∉ (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_790))).fv) := by
  simpa only [nb078_alpha_dummy_801] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_790))).fv) 0

theorem nb078_fresh_947 : (nb078_alpha_dummy_797) ∉ (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) := by
  simpa only [nb078_alpha_dummy_797] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) 0

theorem nb078_fresh_948 : (nb078_alpha_dummy_803) ∉ (((Class.cv (nb078_alpha_dummy_791))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) := by
  simpa only [nb078_alpha_dummy_803] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_791))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) 0

theorem nb078_fresh_949 (h : Var) : (nb078_alpha_dummy_802 h) ∉ (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_793 h))).fv) := by
  simpa only [nb078_alpha_dummy_802] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_793 h))).fv) 0

theorem nb078_fresh_950 (h : Var) : (nb078_alpha_dummy_798 h) ∉ (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) := by
  simpa only [nb078_alpha_dummy_798] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) 0

theorem nb078_fresh_951 (h : Var) : (nb078_alpha_dummy_804 h) ∉ (((Class.cv (nb078_alpha_dummy_794 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) := by
  simpa only [nb078_alpha_dummy_804] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_794 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) 0

theorem nb078_fresh_952 : (nb078_alpha_dummy_819) ∉ (((Class.cv (nb078_alpha_dummy_812))).fv) := by
  simpa only [nb078_alpha_dummy_819] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_812))).fv) 0

theorem nb078_fresh_953 : (nb078_alpha_dummy_820) ∉ (((Class.cv (nb078_alpha_dummy_812))).fv) := by
  simpa only [nb078_alpha_dummy_820] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_812))).fv) 1

theorem nb078_distinct_954 : (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_820) := by
  simpa only [nb078_alpha_dummy_819, nb078_alpha_dummy_820] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_812))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_955 (h : Var) : (nb078_alpha_dummy_821 h) ∉ (((Class.cv (nb078_alpha_dummy_814 h))).fv) := by
  simpa only [nb078_alpha_dummy_821] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_814 h))).fv) 0

theorem nb078_fresh_956 (h : Var) : (nb078_alpha_dummy_822 h) ∉ (((Class.cv (nb078_alpha_dummy_814 h))).fv) := by
  simpa only [nb078_alpha_dummy_822] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_814 h))).fv) 1

theorem nb078_distinct_957 (h : Var) : (nb078_alpha_dummy_821 h) ≠ (nb078_alpha_dummy_822 h) := by
  simpa only [nb078_alpha_dummy_821, nb078_alpha_dummy_822] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_814 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_958 : (nb078_alpha_dummy_825) ∉ (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_825] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_959 : (nb078_alpha_dummy_826) ∉ (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_826] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_960 : (nb078_alpha_dummy_827) ∉ (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_827] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_961 : (nb078_alpha_dummy_825) ≠ (nb078_alpha_dummy_826) := by
  simpa only [nb078_alpha_dummy_825, nb078_alpha_dummy_826] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_962 : (nb078_alpha_dummy_825) ≠ (nb078_alpha_dummy_827) := by
  simpa only [nb078_alpha_dummy_825, nb078_alpha_dummy_827] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_963 : (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_827) := by
  simpa only [nb078_alpha_dummy_826, nb078_alpha_dummy_827] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_964 (h : Var) : (nb078_alpha_dummy_828 h) ∉ (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_828] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_965 (h : Var) : (nb078_alpha_dummy_829 h) ∉ (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_829] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_966 (h : Var) : (nb078_alpha_dummy_830 h) ∉ (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_830] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_967 (h : Var) : (nb078_alpha_dummy_828 h) ≠ (nb078_alpha_dummy_829 h) := by
  simpa only [nb078_alpha_dummy_828, nb078_alpha_dummy_829] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_968 (h : Var) : (nb078_alpha_dummy_828 h) ≠ (nb078_alpha_dummy_830 h) := by
  simpa only [nb078_alpha_dummy_828, nb078_alpha_dummy_830] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_969 (h : Var) : (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_830 h) := by
  simpa only [nb078_alpha_dummy_829, nb078_alpha_dummy_830] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_970 : (nb078_alpha_dummy_837) ∉ (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_826))).fv) := by
  simpa only [nb078_alpha_dummy_837] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_826))).fv) 0

theorem nb078_fresh_971 : (nb078_alpha_dummy_833) ∉ (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) := by
  simpa only [nb078_alpha_dummy_833] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) 0

theorem nb078_fresh_972 : (nb078_alpha_dummy_839) ∉ (((Class.cv (nb078_alpha_dummy_827))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) := by
  simpa only [nb078_alpha_dummy_839] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_827))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) 0

theorem nb078_fresh_973 (h : Var) : (nb078_alpha_dummy_838 h) ∉ (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_829 h))).fv) := by
  simpa only [nb078_alpha_dummy_838] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_829 h))).fv) 0

theorem nb078_fresh_974 (h : Var) : (nb078_alpha_dummy_834 h) ∉ (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) := by
  simpa only [nb078_alpha_dummy_834] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) 0

theorem nb078_fresh_975 (h : Var) : (nb078_alpha_dummy_840 h) ∉ (((Class.cv (nb078_alpha_dummy_830 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) := by
  simpa only [nb078_alpha_dummy_840] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_830 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) 0

theorem nb078_fresh_976 : (nb078_alpha_dummy_853) ∉ (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) := by
  simpa only [nb078_alpha_dummy_853] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) 0

theorem nb078_fresh_977 : (nb078_alpha_dummy_854) ∉ (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) := by
  simpa only [nb078_alpha_dummy_854] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) 1

theorem nb078_distinct_978 : (nb078_alpha_dummy_853) ≠ (nb078_alpha_dummy_854) := by
  simpa only [nb078_alpha_dummy_853, nb078_alpha_dummy_854] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_979 : (nb078_alpha_dummy_889) ∉ (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) := by
  simpa only [nb078_alpha_dummy_889] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) 0

theorem nb078_fresh_980 : (nb078_alpha_dummy_890) ∉ (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) := by
  simpa only [nb078_alpha_dummy_890] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) 1

theorem nb078_distinct_981 : (nb078_alpha_dummy_889) ≠ (nb078_alpha_dummy_890) := by
  simpa only [nb078_alpha_dummy_889, nb078_alpha_dummy_890] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_982 (h : Var) : (nb078_alpha_dummy_855 h) ∉ (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) := by
  simpa only [nb078_alpha_dummy_855] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) 0

theorem nb078_fresh_983 (h : Var) : (nb078_alpha_dummy_856 h) ∉ (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) := by
  simpa only [nb078_alpha_dummy_856] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) 1

theorem nb078_distinct_984 (h : Var) : (nb078_alpha_dummy_855 h) ≠ (nb078_alpha_dummy_856 h) := by
  simpa only [nb078_alpha_dummy_855, nb078_alpha_dummy_856] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_985 (h : Var) : (nb078_alpha_dummy_891 h) ∉ (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) := by
  simpa only [nb078_alpha_dummy_891] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) 0

theorem nb078_fresh_986 (h : Var) : (nb078_alpha_dummy_892 h) ∉ (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) := by
  simpa only [nb078_alpha_dummy_892] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) 1

theorem nb078_distinct_987 (h : Var) : (nb078_alpha_dummy_891 h) ≠ (nb078_alpha_dummy_892 h) := by
  simpa only [nb078_alpha_dummy_891, nb078_alpha_dummy_892] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_988 : (nb078_alpha_dummy_861) ∉ (((Class.cv (nb078_alpha_dummy_854))).fv) := by
  simpa only [nb078_alpha_dummy_861] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_854))).fv) 0

theorem nb078_fresh_989 : (nb078_alpha_dummy_862) ∉ (((Class.cv (nb078_alpha_dummy_854))).fv) := by
  simpa only [nb078_alpha_dummy_862] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_854))).fv) 1

theorem nb078_distinct_990 : (nb078_alpha_dummy_861) ≠ (nb078_alpha_dummy_862) := by
  simpa only [nb078_alpha_dummy_861, nb078_alpha_dummy_862] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_991 (h : Var) : (nb078_alpha_dummy_863 h) ∉ (((Class.cv (nb078_alpha_dummy_856 h))).fv) := by
  simpa only [nb078_alpha_dummy_863] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_856 h))).fv) 0

theorem nb078_fresh_992 (h : Var) : (nb078_alpha_dummy_864 h) ∉ (((Class.cv (nb078_alpha_dummy_856 h))).fv) := by
  simpa only [nb078_alpha_dummy_864] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_856 h))).fv) 1

theorem nb078_distinct_993 (h : Var) : (nb078_alpha_dummy_863 h) ≠ (nb078_alpha_dummy_864 h) := by
  simpa only [nb078_alpha_dummy_863, nb078_alpha_dummy_864] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_856 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_994 : (nb078_alpha_dummy_867) ∉ (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_867] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_995 : (nb078_alpha_dummy_868) ∉ (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_868] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_996 : (nb078_alpha_dummy_869) ∉ (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_869] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_997 : (nb078_alpha_dummy_867) ≠ (nb078_alpha_dummy_868) := by
  simpa only [nb078_alpha_dummy_867, nb078_alpha_dummy_868] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_998 : (nb078_alpha_dummy_867) ≠ (nb078_alpha_dummy_869) := by
  simpa only [nb078_alpha_dummy_867, nb078_alpha_dummy_869] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_999 : (nb078_alpha_dummy_868) ≠ (nb078_alpha_dummy_869) := by
  simpa only [nb078_alpha_dummy_868, nb078_alpha_dummy_869] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1000 (h : Var) : (nb078_alpha_dummy_870 h) ∉ (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_870] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1001 (h : Var) : (nb078_alpha_dummy_871 h) ∉ (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_871] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1002 (h : Var) : (nb078_alpha_dummy_872 h) ∉ (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_872] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1003 (h : Var) : (nb078_alpha_dummy_870 h) ≠ (nb078_alpha_dummy_871 h) := by
  simpa only [nb078_alpha_dummy_870, nb078_alpha_dummy_871] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
