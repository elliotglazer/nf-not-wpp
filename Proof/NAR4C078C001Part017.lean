import NAR4C078C001Part016

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

theorem nb078_distinct_1004 (h : Var) : (nb078_alpha_dummy_870 h) ≠ (nb078_alpha_dummy_872 h) := by
  simpa only [nb078_alpha_dummy_870, nb078_alpha_dummy_872] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1005 (h : Var) : (nb078_alpha_dummy_871 h) ≠ (nb078_alpha_dummy_872 h) := by
  simpa only [nb078_alpha_dummy_871, nb078_alpha_dummy_872] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1006 : (nb078_alpha_dummy_879) ∉ (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_868))).fv) := by
  simpa only [nb078_alpha_dummy_879] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_868))).fv) 0

theorem nb078_fresh_1007 : (nb078_alpha_dummy_875) ∉ (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) := by
  simpa only [nb078_alpha_dummy_875] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) 0

theorem nb078_fresh_1008 : (nb078_alpha_dummy_881) ∉ (((Class.cv (nb078_alpha_dummy_869))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) := by
  simpa only [nb078_alpha_dummy_881] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_869))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) 0

theorem nb078_fresh_1009 (h : Var) : (nb078_alpha_dummy_880 h) ∉ (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_871 h))).fv) := by
  simpa only [nb078_alpha_dummy_880] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_871 h))).fv) 0

theorem nb078_fresh_1010 (h : Var) : (nb078_alpha_dummy_876 h) ∉ (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) := by
  simpa only [nb078_alpha_dummy_876] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) 0

theorem nb078_fresh_1011 (h : Var) : (nb078_alpha_dummy_882 h) ∉ (((Class.cv (nb078_alpha_dummy_872 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) := by
  simpa only [nb078_alpha_dummy_882] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_872 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) 0

theorem nb078_fresh_1012 : (nb078_alpha_dummy_897) ∉ (((Class.cv (nb078_alpha_dummy_890))).fv) := by
  simpa only [nb078_alpha_dummy_897] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_890))).fv) 0

theorem nb078_fresh_1013 : (nb078_alpha_dummy_898) ∉ (((Class.cv (nb078_alpha_dummy_890))).fv) := by
  simpa only [nb078_alpha_dummy_898] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_890))).fv) 1

theorem nb078_distinct_1014 : (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_898) := by
  simpa only [nb078_alpha_dummy_897, nb078_alpha_dummy_898] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_890))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1015 (h : Var) : (nb078_alpha_dummy_899 h) ∉ (((Class.cv (nb078_alpha_dummy_892 h))).fv) := by
  simpa only [nb078_alpha_dummy_899] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_892 h))).fv) 0

theorem nb078_fresh_1016 (h : Var) : (nb078_alpha_dummy_900 h) ∉ (((Class.cv (nb078_alpha_dummy_892 h))).fv) := by
  simpa only [nb078_alpha_dummy_900] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_892 h))).fv) 1

theorem nb078_distinct_1017 (h : Var) : (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_900 h) := by
  simpa only [nb078_alpha_dummy_899, nb078_alpha_dummy_900] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_892 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1018 : (nb078_alpha_dummy_903) ∉ (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_903] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1019 : (nb078_alpha_dummy_904) ∉ (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_904] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1020 : (nb078_alpha_dummy_905) ∉ (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_905] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1021 : (nb078_alpha_dummy_903) ≠ (nb078_alpha_dummy_904) := by
  simpa only [nb078_alpha_dummy_903, nb078_alpha_dummy_904] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1022 : (nb078_alpha_dummy_903) ≠ (nb078_alpha_dummy_905) := by
  simpa only [nb078_alpha_dummy_903, nb078_alpha_dummy_905] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1023 : (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_905) := by
  simpa only [nb078_alpha_dummy_904, nb078_alpha_dummy_905] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1024 (h : Var) : (nb078_alpha_dummy_906 h) ∉ (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_906] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1025 (h : Var) : (nb078_alpha_dummy_907 h) ∉ (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_907] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1026 (h : Var) : (nb078_alpha_dummy_908 h) ∉ (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_908] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1027 (h : Var) : (nb078_alpha_dummy_906 h) ≠ (nb078_alpha_dummy_907 h) := by
  simpa only [nb078_alpha_dummy_906, nb078_alpha_dummy_907] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1028 (h : Var) : (nb078_alpha_dummy_906 h) ≠ (nb078_alpha_dummy_908 h) := by
  simpa only [nb078_alpha_dummy_906, nb078_alpha_dummy_908] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1029 (h : Var) : (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_908 h) := by
  simpa only [nb078_alpha_dummy_907, nb078_alpha_dummy_908] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1030 : (nb078_alpha_dummy_915) ∉ (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_904))).fv) := by
  simpa only [nb078_alpha_dummy_915] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_904))).fv) 0

theorem nb078_fresh_1031 : (nb078_alpha_dummy_911) ∉ (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) := by
  simpa only [nb078_alpha_dummy_911] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) 0

theorem nb078_fresh_1032 : (nb078_alpha_dummy_917) ∉ (((Class.cv (nb078_alpha_dummy_905))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) := by
  simpa only [nb078_alpha_dummy_917] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_905))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) 0

theorem nb078_fresh_1033 (h : Var) : (nb078_alpha_dummy_916 h) ∉ (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_907 h))).fv) := by
  simpa only [nb078_alpha_dummy_916] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_907 h))).fv) 0

theorem nb078_fresh_1034 (h : Var) : (nb078_alpha_dummy_912 h) ∉ (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) := by
  simpa only [nb078_alpha_dummy_912] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) 0

theorem nb078_fresh_1035 (h : Var) : (nb078_alpha_dummy_918 h) ∉ (((Class.cv (nb078_alpha_dummy_908 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) := by
  simpa only [nb078_alpha_dummy_918] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_908 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) 0

theorem nb078_fresh_1036 : (nb078_alpha_dummy_933) ∉ (((Class.cv (nb078_alpha_dummy_926))).fv) := by
  simpa only [nb078_alpha_dummy_933] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_926))).fv) 0

theorem nb078_fresh_1037 : (nb078_alpha_dummy_934) ∉ (((Class.cv (nb078_alpha_dummy_926))).fv) := by
  simpa only [nb078_alpha_dummy_934] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_926))).fv) 1

theorem nb078_distinct_1038 : (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_934) := by
  simpa only [nb078_alpha_dummy_933, nb078_alpha_dummy_934] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_926))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1039 (h : Var) : (nb078_alpha_dummy_935 h) ∉ (((Class.cv (nb078_alpha_dummy_928 h))).fv) := by
  simpa only [nb078_alpha_dummy_935] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_928 h))).fv) 0

theorem nb078_fresh_1040 (h : Var) : (nb078_alpha_dummy_936 h) ∉ (((Class.cv (nb078_alpha_dummy_928 h))).fv) := by
  simpa only [nb078_alpha_dummy_936] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_928 h))).fv) 1

theorem nb078_distinct_1041 (h : Var) : (nb078_alpha_dummy_935 h) ≠ (nb078_alpha_dummy_936 h) := by
  simpa only [nb078_alpha_dummy_935, nb078_alpha_dummy_936] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_928 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1042 : (nb078_alpha_dummy_939) ∉ (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_939] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1043 : (nb078_alpha_dummy_940) ∉ (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_940] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1044 : (nb078_alpha_dummy_941) ∉ (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_941] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1045 : (nb078_alpha_dummy_939) ≠ (nb078_alpha_dummy_940) := by
  simpa only [nb078_alpha_dummy_939, nb078_alpha_dummy_940] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1046 : (nb078_alpha_dummy_939) ≠ (nb078_alpha_dummy_941) := by
  simpa only [nb078_alpha_dummy_939, nb078_alpha_dummy_941] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1047 : (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_941) := by
  simpa only [nb078_alpha_dummy_940, nb078_alpha_dummy_941] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1048 (h : Var) : (nb078_alpha_dummy_942 h) ∉ (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_942] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1049 (h : Var) : (nb078_alpha_dummy_943 h) ∉ (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_943] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1050 (h : Var) : (nb078_alpha_dummy_944 h) ∉ (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_944] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1051 (h : Var) : (nb078_alpha_dummy_942 h) ≠ (nb078_alpha_dummy_943 h) := by
  simpa only [nb078_alpha_dummy_942, nb078_alpha_dummy_943] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1052 (h : Var) : (nb078_alpha_dummy_942 h) ≠ (nb078_alpha_dummy_944 h) := by
  simpa only [nb078_alpha_dummy_942, nb078_alpha_dummy_944] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1053 (h : Var) : (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_944 h) := by
  simpa only [nb078_alpha_dummy_943, nb078_alpha_dummy_944] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1054 : (nb078_alpha_dummy_951) ∉ (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_940))).fv) := by
  simpa only [nb078_alpha_dummy_951] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_940))).fv) 0

theorem nb078_fresh_1055 : (nb078_alpha_dummy_947) ∉ (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) := by
  simpa only [nb078_alpha_dummy_947] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) 0

theorem nb078_fresh_1056 : (nb078_alpha_dummy_953) ∉ (((Class.cv (nb078_alpha_dummy_941))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) := by
  simpa only [nb078_alpha_dummy_953] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_941))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) 0

theorem nb078_fresh_1057 (h : Var) : (nb078_alpha_dummy_952 h) ∉ (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_943 h))).fv) := by
  simpa only [nb078_alpha_dummy_952] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_943 h))).fv) 0

theorem nb078_fresh_1058 (h : Var) : (nb078_alpha_dummy_948 h) ∉ (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) := by
  simpa only [nb078_alpha_dummy_948] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) 0

theorem nb078_fresh_1059 (h : Var) : (nb078_alpha_dummy_954 h) ∉ (((Class.cv (nb078_alpha_dummy_944 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) := by
  simpa only [nb078_alpha_dummy_954] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_944 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) 0

theorem nb078_fresh_1060 : (nb078_alpha_dummy_965) ∉ (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) := by
  simpa only [nb078_alpha_dummy_965] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) 0

theorem nb078_fresh_1061 : (nb078_alpha_dummy_966) ∉ (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) := by
  simpa only [nb078_alpha_dummy_966] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) 1

theorem nb078_distinct_1062 : (nb078_alpha_dummy_965) ≠ (nb078_alpha_dummy_966) := by
  simpa only [nb078_alpha_dummy_965, nb078_alpha_dummy_966] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1063 (h : Var) : (nb078_alpha_dummy_967 h) ∉ (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) := by
  simpa only [nb078_alpha_dummy_967] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) 0

theorem nb078_fresh_1064 (h : Var) : (nb078_alpha_dummy_968 h) ∉ (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) := by
  simpa only [nb078_alpha_dummy_968] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) 1

theorem nb078_distinct_1065 (h : Var) : (nb078_alpha_dummy_967 h) ≠ (nb078_alpha_dummy_968 h) := by
  simpa only [nb078_alpha_dummy_967, nb078_alpha_dummy_968] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1066 : (nb078_alpha_dummy_973) ∉ (((Class.cv (nb078_alpha_dummy_966))).fv) := by
  simpa only [nb078_alpha_dummy_973] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_966))).fv) 0

theorem nb078_fresh_1067 : (nb078_alpha_dummy_974) ∉ (((Class.cv (nb078_alpha_dummy_966))).fv) := by
  simpa only [nb078_alpha_dummy_974] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_966))).fv) 1

theorem nb078_distinct_1068 : (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_974) := by
  simpa only [nb078_alpha_dummy_973, nb078_alpha_dummy_974] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_966))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1069 (h : Var) : (nb078_alpha_dummy_975 h) ∉ (((Class.cv (nb078_alpha_dummy_968 h))).fv) := by
  simpa only [nb078_alpha_dummy_975] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_968 h))).fv) 0

theorem nb078_fresh_1070 (h : Var) : (nb078_alpha_dummy_976 h) ∉ (((Class.cv (nb078_alpha_dummy_968 h))).fv) := by
  simpa only [nb078_alpha_dummy_976] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_968 h))).fv) 1

theorem nb078_distinct_1071 (h : Var) : (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_976 h) := by
  simpa only [nb078_alpha_dummy_975, nb078_alpha_dummy_976] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_968 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1072 : (nb078_alpha_dummy_979) ∉ (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_979] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1073 : (nb078_alpha_dummy_980) ∉ (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_980] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1074 : (nb078_alpha_dummy_981) ∉ (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_981] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1075 : (nb078_alpha_dummy_979) ≠ (nb078_alpha_dummy_980) := by
  simpa only [nb078_alpha_dummy_979, nb078_alpha_dummy_980] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1076 : (nb078_alpha_dummy_979) ≠ (nb078_alpha_dummy_981) := by
  simpa only [nb078_alpha_dummy_979, nb078_alpha_dummy_981] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1077 : (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_981) := by
  simpa only [nb078_alpha_dummy_980, nb078_alpha_dummy_981] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1078 (h : Var) : (nb078_alpha_dummy_982 h) ∉ (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_982] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_1079 (h : Var) : (nb078_alpha_dummy_983 h) ∉ (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_983] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_1080 (h : Var) : (nb078_alpha_dummy_984 h) ∉ (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_984] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_1081 (h : Var) : (nb078_alpha_dummy_982 h) ≠ (nb078_alpha_dummy_983 h) := by
  simpa only [nb078_alpha_dummy_982, nb078_alpha_dummy_983] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1082 (h : Var) : (nb078_alpha_dummy_982 h) ≠ (nb078_alpha_dummy_984 h) := by
  simpa only [nb078_alpha_dummy_982, nb078_alpha_dummy_984] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1083 (h : Var) : (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_984 h) := by
  simpa only [nb078_alpha_dummy_983, nb078_alpha_dummy_984] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1084 : (nb078_alpha_dummy_991) ∉ (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_980))).fv) := by
  simpa only [nb078_alpha_dummy_991] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_980))).fv) 0

theorem nb078_fresh_1085 : (nb078_alpha_dummy_987) ∉ (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) := by
  simpa only [nb078_alpha_dummy_987] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) 0

theorem nb078_fresh_1086 : (nb078_alpha_dummy_993) ∉ (((Class.cv (nb078_alpha_dummy_981))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) := by
  simpa only [nb078_alpha_dummy_993] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_981))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) 0

theorem nb078_fresh_1087 (h : Var) : (nb078_alpha_dummy_992 h) ∉ (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_983 h))).fv) := by
  simpa only [nb078_alpha_dummy_992] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_983 h))).fv) 0

theorem nb078_fresh_1088 (h : Var) : (nb078_alpha_dummy_988 h) ∉ (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) := by
  simpa only [nb078_alpha_dummy_988] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) 0

theorem nb078_fresh_1089 (h : Var) : (nb078_alpha_dummy_994 h) ∉ (((Class.cv (nb078_alpha_dummy_984 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) := by
  simpa only [nb078_alpha_dummy_994] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_984 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) 0

theorem nb078_fresh_1090 (f : Var) : (nb078_alpha_dummy_091 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb078_alpha_dummy_091] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb078_fresh_1091 (f : Var) : (nb078_alpha_dummy_092 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb078_alpha_dummy_092] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb078_distinct_1092 (f : Var) : (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_092 f) := by
  simpa only [nb078_alpha_dummy_091, nb078_alpha_dummy_092] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1093 (f : Var) : (nb078_alpha_dummy_012 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb078_alpha_dummy_012] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb078_fresh_1094 (f : Var) : (nb078_alpha_dummy_013 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb078_alpha_dummy_013] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb078_fresh_1095 (f : Var) : (nb078_alpha_dummy_014 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb078_alpha_dummy_014] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb078_distinct_1096 (f : Var) : (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_013 f) := by
  simpa only [nb078_alpha_dummy_012, nb078_alpha_dummy_013] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1097 (f : Var) : (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_014 f) := by
  simpa only [nb078_alpha_dummy_012, nb078_alpha_dummy_014] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1098 (f : Var) : (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_014 f) := by
  simpa only [nb078_alpha_dummy_013, nb078_alpha_dummy_014] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1099 (f : Var) : (nb078_alpha_dummy_245 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_245] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1100 (f : Var) : (nb078_alpha_dummy_246 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_246] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1101 (f : Var) : (nb078_alpha_dummy_245 f) ≠ (nb078_alpha_dummy_246 f) := by
  simpa only [nb078_alpha_dummy_245, nb078_alpha_dummy_246] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1102 (g : Var) : (nb078_alpha_dummy_369 g) ∉ (((Class.cv g)).fv) := by
  simpa only [nb078_alpha_dummy_369] using freshVar_not_mem (((Class.cv g)).fv) 0

theorem nb078_fresh_1103 (g : Var) : (nb078_alpha_dummy_370 g) ∉ (((Class.cv g)).fv) := by
  simpa only [nb078_alpha_dummy_370] using freshVar_not_mem (((Class.cv g)).fv) 1

theorem nb078_distinct_1104 (g : Var) : (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_370 g) := by
  simpa only [nb078_alpha_dummy_369, nb078_alpha_dummy_370] using
    (freshVar_injective (((Class.cv g)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1105 (g : Var) : (nb078_alpha_dummy_290 g) ∉ (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) := by
  simpa only [nb078_alpha_dummy_290] using freshVar_not_mem (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 0

theorem nb078_fresh_1106 (g : Var) : (nb078_alpha_dummy_291 g) ∉ (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) := by
  simpa only [nb078_alpha_dummy_291] using freshVar_not_mem (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 1

theorem nb078_fresh_1107 (g : Var) : (nb078_alpha_dummy_292 g) ∉ (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) := by
  simpa only [nb078_alpha_dummy_292] using freshVar_not_mem (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) 2

theorem nb078_distinct_1108 (g : Var) : (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_291 g) := by
  simpa only [nb078_alpha_dummy_290, nb078_alpha_dummy_291] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1109 (g : Var) : (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_292 g) := by
  simpa only [nb078_alpha_dummy_290, nb078_alpha_dummy_292] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1110 (g : Var) : (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_292 g) := by
  simpa only [nb078_alpha_dummy_291, nb078_alpha_dummy_292] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1111 (g : Var) : (nb078_alpha_dummy_527 g) ∉ (((Class.cv g)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_527] using freshVar_not_mem (((Class.cv g)).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1112 (g : Var) : (nb078_alpha_dummy_528 g) ∉ (((Class.cv g)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_528] using freshVar_not_mem (((Class.cv g)).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1113 (g : Var) : (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_528 g) := by
  simpa only [nb078_alpha_dummy_527, nb078_alpha_dummy_528] using
    (freshVar_injective (((Class.cv g)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1114 (h : Var) : (nb078_alpha_dummy_849 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb078_alpha_dummy_849] using freshVar_not_mem (((Class.cv h)).fv) 0

theorem nb078_fresh_1115 (h : Var) : (nb078_alpha_dummy_850 h) ∉ (((Class.cv h)).fv) := by
  simpa only [nb078_alpha_dummy_850] using freshVar_not_mem (((Class.cv h)).fv) 1

theorem nb078_distinct_1116 (h : Var) : (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_850 h) := by
  simpa only [nb078_alpha_dummy_849, nb078_alpha_dummy_850] using
    (freshVar_injective (((Class.cv h)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1117 (h : Var) : (nb078_alpha_dummy_770 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb078_alpha_dummy_770] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 0

theorem nb078_fresh_1118 (h : Var) : (nb078_alpha_dummy_771 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb078_alpha_dummy_771] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 1

theorem nb078_fresh_1119 (h : Var) : (nb078_alpha_dummy_772 h) ∉ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb078_alpha_dummy_772] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 2

theorem nb078_distinct_1120 (h : Var) : (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_771 h) := by
  simpa only [nb078_alpha_dummy_770, nb078_alpha_dummy_771] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1121 (h : Var) : (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_772 h) := by
  simpa only [nb078_alpha_dummy_770, nb078_alpha_dummy_772] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1122 (h : Var) : (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_772 h) := by
  simpa only [nb078_alpha_dummy_771, nb078_alpha_dummy_772] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1123 (h : Var) : (nb078_alpha_dummy_1007 h) ∉ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_1007] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1124 (h : Var) : (nb078_alpha_dummy_1008 h) ∉ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_1008] using freshVar_not_mem (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1125 (h : Var) : (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1008 h) := by
  simpa only [nb078_alpha_dummy_1007, nb078_alpha_dummy_1008] using
    (freshVar_injective (((Class.cv h)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1126 : (nb078_alpha_dummy_029) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_025)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_025)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_025))).fv) := by
  simpa only [nb078_alpha_dummy_029] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_025)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_025)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_025))).fv) 0

theorem nb078_fresh_1127 (f : Var) : (nb078_alpha_dummy_030 f) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_027 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_027 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_027 f))).fv) := by
  simpa only [nb078_alpha_dummy_030] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_027 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_027 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_027 f))).fv) 0

theorem nb078_fresh_1128 : (nb078_alpha_dummy_065) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_061)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_061)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_061))).fv) := by
  simpa only [nb078_alpha_dummy_065] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_061)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_061)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_061))).fv) 0

theorem nb078_fresh_1129 (f : Var) : (nb078_alpha_dummy_066 f) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_063 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_063 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_063 f))).fv) := by
  simpa only [nb078_alpha_dummy_066] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_063 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_063 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_063 f))).fv) 0

theorem nb078_fresh_1130 : (nb078_alpha_dummy_1021) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1017)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1017)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1017))).fv) := by
  simpa only [nb078_alpha_dummy_1021] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1017)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1017)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1017))).fv) 0

theorem nb078_fresh_1131 (h : Var) : (nb078_alpha_dummy_1022 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1019 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1019 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1019 h))).fv) := by
  simpa only [nb078_alpha_dummy_1022] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1019 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1019 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1019 h))).fv) 0

theorem nb078_fresh_1132 : (nb078_alpha_dummy_107) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_103)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_103)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_103))).fv) := by
  simpa only [nb078_alpha_dummy_107] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_103)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_103)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_103))).fv) 0

theorem nb078_fresh_1133 (f : Var) : (nb078_alpha_dummy_108 f) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_105 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_105 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_105 f))).fv) := by
  simpa only [nb078_alpha_dummy_108] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_105 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_105 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_105 f))).fv) 0

theorem nb078_fresh_1134 : (nb078_alpha_dummy_1069) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1065)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1065)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1065))).fv) := by
  simpa only [nb078_alpha_dummy_1069] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1065)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1065)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1065))).fv) 0

theorem nb078_fresh_1135 (h : Var) : (nb078_alpha_dummy_1070 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1067 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1067 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1067 h))).fv) := by
  simpa only [nb078_alpha_dummy_1070] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1067 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1067 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1067 h))).fv) 0

theorem nb078_fresh_1136 : (nb078_alpha_dummy_1105) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1101)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1101)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1101))).fv) := by
  simpa only [nb078_alpha_dummy_1105] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1101)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1101)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1101))).fv) 0

theorem nb078_fresh_1137 (h : Var) : (nb078_alpha_dummy_1106 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1103 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1103 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1103 h))).fv) := by
  simpa only [nb078_alpha_dummy_1106] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1103 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1103 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1103 h))).fv) 0

theorem nb078_fresh_1138 : (nb078_alpha_dummy_1147) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1143)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1143)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1143))).fv) := by
  simpa only [nb078_alpha_dummy_1147] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1143)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1143)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1143))).fv) 0

theorem nb078_fresh_1139 (h : Var) : (nb078_alpha_dummy_1148 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1145 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1145 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1145 h))).fv) := by
  simpa only [nb078_alpha_dummy_1148] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1145 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1145 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1145 h))).fv) 0

theorem nb078_fresh_1140 : (nb078_alpha_dummy_1183) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1179)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1179)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1179))).fv) := by
  simpa only [nb078_alpha_dummy_1183] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1179)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1179)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1179))).fv) 0

theorem nb078_fresh_1141 (h : Var) : (nb078_alpha_dummy_1184 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1181 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1181 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1181 h))).fv) := by
  simpa only [nb078_alpha_dummy_1184] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1181 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1181 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1181 h))).fv) 0

theorem nb078_fresh_1142 : (nb078_alpha_dummy_1219) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1215)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1215)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1215))).fv) := by
  simpa only [nb078_alpha_dummy_1219] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1215)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1215)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1215))).fv) 0

theorem nb078_fresh_1143 (h : Var) : (nb078_alpha_dummy_1220 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_1217 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1217 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1217 h))).fv) := by
  simpa only [nb078_alpha_dummy_1220] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_1217 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1217 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1217 h))).fv) 0

theorem nb078_fresh_1144 : (nb078_alpha_dummy_143) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_139)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_139)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_139))).fv) := by
  simpa only [nb078_alpha_dummy_143] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_139)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_139)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_139))).fv) 0

theorem nb078_fresh_1145 (f : Var) : (nb078_alpha_dummy_144 f) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_141 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_141 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_141 f))).fv) := by
  simpa only [nb078_alpha_dummy_144] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_141 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_141 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_141 f))).fv) 0

theorem nb078_fresh_1146 : (nb078_alpha_dummy_179) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_175)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_175)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_175))).fv) := by
  simpa only [nb078_alpha_dummy_179] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_175)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_175)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_175))).fv) 0

theorem nb078_fresh_1147 (f : Var) : (nb078_alpha_dummy_180 f) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_177 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_177 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_177 f))).fv) := by
  simpa only [nb078_alpha_dummy_180] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_177 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_177 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_177 f))).fv) 0

theorem nb078_fresh_1148 : (nb078_alpha_dummy_219) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_215)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_215)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_215))).fv) := by
  simpa only [nb078_alpha_dummy_219] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_215)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_215)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_215))).fv) 0

theorem nb078_fresh_1149 (f : Var) : (nb078_alpha_dummy_220 f) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_217 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_217 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_217 f))).fv) := by
  simpa only [nb078_alpha_dummy_220] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_217 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_217 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_217 f))).fv) 0

theorem nb078_fresh_1150 : (nb078_alpha_dummy_259) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_255)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_255)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_255))).fv) := by
  simpa only [nb078_alpha_dummy_259] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_255)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_255)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_255))).fv) 0

theorem nb078_fresh_1151 (f : Var) : (nb078_alpha_dummy_260 f) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_257 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_257 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_257 f))).fv) := by
  simpa only [nb078_alpha_dummy_260] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_257 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_257 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_257 f))).fv) 0

theorem nb078_fresh_1152 : (nb078_alpha_dummy_307) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_303)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_303)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_303))).fv) := by
  simpa only [nb078_alpha_dummy_307] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_303)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_303)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_303))).fv) 0

theorem nb078_fresh_1153 (g : Var) : (nb078_alpha_dummy_308 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_305 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_305 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_305 g))).fv) := by
  simpa only [nb078_alpha_dummy_308] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_305 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_305 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_305 g))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
