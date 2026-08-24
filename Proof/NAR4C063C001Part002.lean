import NAR4C063C001Part001

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

theorem nb063_distinct_036 (r : Var) (a : Var) : (nb063_alpha_dummy_023 r a) ≠ (nb063_alpha_dummy_024 r a) := by
  simpa only [nb063_alpha_dummy_023, nb063_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_distinct_037 (r : Var) (a : Var) : (nb063_alpha_dummy_023 r a) ≠ (nb063_alpha_dummy_025 r a) := by
  simpa only [nb063_alpha_dummy_023, nb063_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb063_distinct_038 (r : Var) (a : Var) : (nb063_alpha_dummy_024 r a) ≠ (nb063_alpha_dummy_025 r a) := by
  simpa only [nb063_alpha_dummy_024, nb063_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb063_fresh_039 : (nb063_alpha_dummy_032) ∉ (((Class.cv (nb063_alpha_dummy_021))).fv ∪ ((Class.cv (nb063_alpha_dummy_021))).fv) := by
  simpa only [nb063_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_021))).fv ∪ ((Class.cv (nb063_alpha_dummy_021))).fv) 0

theorem nb063_fresh_040 : (nb063_alpha_dummy_028) ∉ (((Class.cv (nb063_alpha_dummy_021))).fv ∪ ((Class.cv (nb063_alpha_dummy_022))).fv) := by
  simpa only [nb063_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_021))).fv ∪ ((Class.cv (nb063_alpha_dummy_022))).fv) 0

theorem nb063_fresh_041 : (nb063_alpha_dummy_034) ∉ (((Class.cv (nb063_alpha_dummy_022))).fv ∪ ((Class.cv (nb063_alpha_dummy_022))).fv) := by
  simpa only [nb063_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_022))).fv ∪ ((Class.cv (nb063_alpha_dummy_022))).fv) 0

theorem nb063_fresh_042 (r : Var) (a : Var) : (nb063_alpha_dummy_033 r a) ∉ (((Class.cv (nb063_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb063_alpha_dummy_024 r a))).fv) := by
  simpa only [nb063_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb063_alpha_dummy_024 r a))).fv) 0

theorem nb063_fresh_043 (r : Var) (a : Var) : (nb063_alpha_dummy_029 r a) ∉ (((Class.cv (nb063_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb063_alpha_dummy_025 r a))).fv) := by
  simpa only [nb063_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb063_alpha_dummy_025 r a))).fv) 0

theorem nb063_fresh_044 (r : Var) (a : Var) : (nb063_alpha_dummy_035 r a) ∉ (((Class.cv (nb063_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb063_alpha_dummy_025 r a))).fv) := by
  simpa only [nb063_alpha_dummy_035] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb063_alpha_dummy_025 r a))).fv) 0

theorem nb063_fresh_045 : (nb063_alpha_dummy_050) ∉ (((Class.cv (nb063_alpha_dummy_043))).fv) := by
  simpa only [nb063_alpha_dummy_050] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_043))).fv) 0

theorem nb063_fresh_046 : (nb063_alpha_dummy_051) ∉ (((Class.cv (nb063_alpha_dummy_043))).fv) := by
  simpa only [nb063_alpha_dummy_051] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_043))).fv) 1

theorem nb063_distinct_047 : (nb063_alpha_dummy_050) ≠ (nb063_alpha_dummy_051) := by
  simpa only [nb063_alpha_dummy_050, nb063_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_043))).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_048 (x : Var) (y : Var) : (nb063_alpha_dummy_052 x y) ∉ (((Class.cv (nb063_alpha_dummy_045 x y))).fv) := by
  simpa only [nb063_alpha_dummy_052] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_045 x y))).fv) 0

theorem nb063_fresh_049 (x : Var) (y : Var) : (nb063_alpha_dummy_053 x y) ∉ (((Class.cv (nb063_alpha_dummy_045 x y))).fv) := by
  simpa only [nb063_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_045 x y))).fv) 1

theorem nb063_distinct_050 (x : Var) (y : Var) : (nb063_alpha_dummy_052 x y) ≠ (nb063_alpha_dummy_053 x y) := by
  simpa only [nb063_alpha_dummy_052, nb063_alpha_dummy_053] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_045 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_051 : (nb063_alpha_dummy_056) ∉ (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 0

theorem nb063_fresh_052 : (nb063_alpha_dummy_057) ∉ (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_057] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 1

theorem nb063_fresh_053 : (nb063_alpha_dummy_058) ∉ (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_058] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) 2

theorem nb063_distinct_054 : (nb063_alpha_dummy_056) ≠ (nb063_alpha_dummy_057) := by
  simpa only [nb063_alpha_dummy_056, nb063_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_distinct_055 : (nb063_alpha_dummy_056) ≠ (nb063_alpha_dummy_058) := by
  simpa only [nb063_alpha_dummy_056, nb063_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb063_distinct_056 : (nb063_alpha_dummy_057) ≠ (nb063_alpha_dummy_058) := by
  simpa only [nb063_alpha_dummy_057, nb063_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb063_fresh_057 (x : Var) (y : Var) : (nb063_alpha_dummy_059 x y) ∉ (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb063_fresh_058 (x : Var) (y : Var) : (nb063_alpha_dummy_060 x y) ∉ (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb063_fresh_059 (x : Var) (y : Var) : (nb063_alpha_dummy_061 x y) ∉ (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb063_distinct_060 (x : Var) (y : Var) : (nb063_alpha_dummy_059 x y) ≠ (nb063_alpha_dummy_060 x y) := by
  simpa only [nb063_alpha_dummy_059, nb063_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_distinct_061 (x : Var) (y : Var) : (nb063_alpha_dummy_059 x y) ≠ (nb063_alpha_dummy_061 x y) := by
  simpa only [nb063_alpha_dummy_059, nb063_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb063_distinct_062 (x : Var) (y : Var) : (nb063_alpha_dummy_060 x y) ≠ (nb063_alpha_dummy_061 x y) := by
  simpa only [nb063_alpha_dummy_060, nb063_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb063_fresh_063 : (nb063_alpha_dummy_068) ∉ (((Class.cv (nb063_alpha_dummy_057))).fv ∪ ((Class.cv (nb063_alpha_dummy_057))).fv) := by
  simpa only [nb063_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_057))).fv ∪ ((Class.cv (nb063_alpha_dummy_057))).fv) 0

theorem nb063_fresh_064 : (nb063_alpha_dummy_064) ∉ (((Class.cv (nb063_alpha_dummy_057))).fv ∪ ((Class.cv (nb063_alpha_dummy_058))).fv) := by
  simpa only [nb063_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_057))).fv ∪ ((Class.cv (nb063_alpha_dummy_058))).fv) 0

theorem nb063_fresh_065 : (nb063_alpha_dummy_070) ∉ (((Class.cv (nb063_alpha_dummy_058))).fv ∪ ((Class.cv (nb063_alpha_dummy_058))).fv) := by
  simpa only [nb063_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_058))).fv ∪ ((Class.cv (nb063_alpha_dummy_058))).fv) 0

theorem nb063_fresh_066 (x : Var) (y : Var) : (nb063_alpha_dummy_069 x y) ∉ (((Class.cv (nb063_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_060 x y))).fv) := by
  simpa only [nb063_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_060 x y))).fv) 0

theorem nb063_fresh_067 (x : Var) (y : Var) : (nb063_alpha_dummy_065 x y) ∉ (((Class.cv (nb063_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_061 x y))).fv) := by
  simpa only [nb063_alpha_dummy_065] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_061 x y))).fv) 0

theorem nb063_fresh_068 (x : Var) (y : Var) : (nb063_alpha_dummy_071 x y) ∉ (((Class.cv (nb063_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_061 x y))).fv) := by
  simpa only [nb063_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_061 x y))).fv) 0

theorem nb063_fresh_069 : (nb063_alpha_dummy_086) ∉ (((Class.cv (nb063_alpha_dummy_079))).fv) := by
  simpa only [nb063_alpha_dummy_086] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_079))).fv) 0

theorem nb063_fresh_070 : (nb063_alpha_dummy_087) ∉ (((Class.cv (nb063_alpha_dummy_079))).fv) := by
  simpa only [nb063_alpha_dummy_087] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_079))).fv) 1

theorem nb063_distinct_071 : (nb063_alpha_dummy_086) ≠ (nb063_alpha_dummy_087) := by
  simpa only [nb063_alpha_dummy_086, nb063_alpha_dummy_087] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_079))).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_072 (x : Var) (y : Var) : (nb063_alpha_dummy_088 x y) ∉ (((Class.cv (nb063_alpha_dummy_081 x y))).fv) := by
  simpa only [nb063_alpha_dummy_088] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_081 x y))).fv) 0

theorem nb063_fresh_073 (x : Var) (y : Var) : (nb063_alpha_dummy_089 x y) ∉ (((Class.cv (nb063_alpha_dummy_081 x y))).fv) := by
  simpa only [nb063_alpha_dummy_089] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_081 x y))).fv) 1

theorem nb063_distinct_074 (x : Var) (y : Var) : (nb063_alpha_dummy_088 x y) ≠ (nb063_alpha_dummy_089 x y) := by
  simpa only [nb063_alpha_dummy_088, nb063_alpha_dummy_089] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_081 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_075 : (nb063_alpha_dummy_092) ∉ (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_092] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 0

theorem nb063_fresh_076 : (nb063_alpha_dummy_093) ∉ (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_093] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 1

theorem nb063_fresh_077 : (nb063_alpha_dummy_094) ∉ (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_094] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) 2

theorem nb063_distinct_078 : (nb063_alpha_dummy_092) ≠ (nb063_alpha_dummy_093) := by
  simpa only [nb063_alpha_dummy_092, nb063_alpha_dummy_093] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_distinct_079 : (nb063_alpha_dummy_092) ≠ (nb063_alpha_dummy_094) := by
  simpa only [nb063_alpha_dummy_092, nb063_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb063_distinct_080 : (nb063_alpha_dummy_093) ≠ (nb063_alpha_dummy_094) := by
  simpa only [nb063_alpha_dummy_093, nb063_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb063_fresh_081 (x : Var) (y : Var) : (nb063_alpha_dummy_095 x y) ∉ (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_095] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb063_fresh_082 (x : Var) (y : Var) : (nb063_alpha_dummy_096 x y) ∉ (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_096] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb063_fresh_083 (x : Var) (y : Var) : (nb063_alpha_dummy_097 x y) ∉ (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb063_alpha_dummy_097] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb063_distinct_084 (x : Var) (y : Var) : (nb063_alpha_dummy_095 x y) ≠ (nb063_alpha_dummy_096 x y) := by
  simpa only [nb063_alpha_dummy_095, nb063_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_distinct_085 (x : Var) (y : Var) : (nb063_alpha_dummy_095 x y) ≠ (nb063_alpha_dummy_097 x y) := by
  simpa only [nb063_alpha_dummy_095, nb063_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb063_distinct_086 (x : Var) (y : Var) : (nb063_alpha_dummy_096 x y) ≠ (nb063_alpha_dummy_097 x y) := by
  simpa only [nb063_alpha_dummy_096, nb063_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb063_fresh_087 : (nb063_alpha_dummy_104) ∉ (((Class.cv (nb063_alpha_dummy_093))).fv ∪ ((Class.cv (nb063_alpha_dummy_093))).fv) := by
  simpa only [nb063_alpha_dummy_104] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_093))).fv ∪ ((Class.cv (nb063_alpha_dummy_093))).fv) 0

theorem nb063_fresh_088 : (nb063_alpha_dummy_100) ∉ (((Class.cv (nb063_alpha_dummy_093))).fv ∪ ((Class.cv (nb063_alpha_dummy_094))).fv) := by
  simpa only [nb063_alpha_dummy_100] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_093))).fv ∪ ((Class.cv (nb063_alpha_dummy_094))).fv) 0

theorem nb063_fresh_089 : (nb063_alpha_dummy_106) ∉ (((Class.cv (nb063_alpha_dummy_094))).fv ∪ ((Class.cv (nb063_alpha_dummy_094))).fv) := by
  simpa only [nb063_alpha_dummy_106] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_094))).fv ∪ ((Class.cv (nb063_alpha_dummy_094))).fv) 0

theorem nb063_fresh_090 (x : Var) (y : Var) : (nb063_alpha_dummy_105 x y) ∉ (((Class.cv (nb063_alpha_dummy_096 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_096 x y))).fv) := by
  simpa only [nb063_alpha_dummy_105] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_096 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_096 x y))).fv) 0

theorem nb063_fresh_091 (x : Var) (y : Var) : (nb063_alpha_dummy_101 x y) ∉ (((Class.cv (nb063_alpha_dummy_096 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_097 x y))).fv) := by
  simpa only [nb063_alpha_dummy_101] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_096 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_097 x y))).fv) 0

theorem nb063_fresh_092 (x : Var) (y : Var) : (nb063_alpha_dummy_107 x y) ∉ (((Class.cv (nb063_alpha_dummy_097 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_097 x y))).fv) := by
  simpa only [nb063_alpha_dummy_107] using freshVar_not_mem (((Class.cv (nb063_alpha_dummy_097 x y))).fv ∪ ((Class.cv (nb063_alpha_dummy_097 x y))).fv) 0

theorem nb063_fresh_093 (r : Var) (a : Var) : (nb063_alpha_dummy_008 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb063_alpha_dummy_008] using freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb063_fresh_094 (r : Var) (a : Var) : (nb063_alpha_dummy_009 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb063_alpha_dummy_009] using freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb063_distinct_095 (r : Var) (a : Var) : (nb063_alpha_dummy_008 r a) ≠ (nb063_alpha_dummy_009 r a) := by
  simpa only [nb063_alpha_dummy_008, nb063_alpha_dummy_009] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_096 (x : Var) (y : Var) : (nb063_alpha_dummy_044 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb063_alpha_dummy_044] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb063_fresh_097 (x : Var) (y : Var) : (nb063_alpha_dummy_045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb063_alpha_dummy_045] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb063_distinct_098 (x : Var) (y : Var) : (nb063_alpha_dummy_044 x y) ≠ (nb063_alpha_dummy_045 x y) := by
  simpa only [nb063_alpha_dummy_044, nb063_alpha_dummy_045] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_099 (x : Var) (y : Var) : (nb063_alpha_dummy_080 x y) ∉ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb063_alpha_dummy_080] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 0

theorem nb063_fresh_100 (x : Var) (y : Var) : (nb063_alpha_dummy_081 x y) ∉ (((Class.cv y)).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb063_alpha_dummy_081] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv x)).fv) 1

theorem nb063_distinct_101 (x : Var) (y : Var) : (nb063_alpha_dummy_080 x y) ≠ (nb063_alpha_dummy_081 x y) := by
  simpa only [nb063_alpha_dummy_080, nb063_alpha_dummy_081] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb063_fresh_102 : (nb063_alpha_dummy_018) ∉ (((Wff.classMem (Class.cv (nb063_alpha_dummy_014)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_014)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_014))).fv) := by
  simpa only [nb063_alpha_dummy_018] using freshVar_not_mem (((Wff.classMem (Class.cv (nb063_alpha_dummy_014)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_014)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_014))).fv) 0

theorem nb063_fresh_103 (r : Var) (a : Var) : (nb063_alpha_dummy_019 r a) ∉ (((Wff.classMem (Class.cv (nb063_alpha_dummy_016 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_016 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_016 r a))).fv) := by
  simpa only [nb063_alpha_dummy_019] using freshVar_not_mem (((Wff.classMem (Class.cv (nb063_alpha_dummy_016 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_016 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_016 r a))).fv) 0

theorem nb063_fresh_104 : (nb063_alpha_dummy_054) ∉ (((Wff.classMem (Class.cv (nb063_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_050))).fv) := by
  simpa only [nb063_alpha_dummy_054] using freshVar_not_mem (((Wff.classMem (Class.cv (nb063_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_050))).fv) 0

theorem nb063_fresh_105 (x : Var) (y : Var) : (nb063_alpha_dummy_055 x y) ∉ (((Wff.classMem (Class.cv (nb063_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_052 x y))).fv) := by
  simpa only [nb063_alpha_dummy_055] using freshVar_not_mem (((Wff.classMem (Class.cv (nb063_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_052 x y))).fv) 0

theorem nb063_fresh_106 : (nb063_alpha_dummy_090) ∉ (((Wff.classMem (Class.cv (nb063_alpha_dummy_086)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_086)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_086))).fv) := by
  simpa only [nb063_alpha_dummy_090] using freshVar_not_mem (((Wff.classMem (Class.cv (nb063_alpha_dummy_086)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_086)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_086))).fv) 0

theorem nb063_fresh_107 (x : Var) (y : Var) : (nb063_alpha_dummy_091 x y) ∉ (((Wff.classMem (Class.cv (nb063_alpha_dummy_088 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_088 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_088 x y))).fv) := by
  simpa only [nb063_alpha_dummy_091] using freshVar_not_mem (((Wff.classMem (Class.cv (nb063_alpha_dummy_088 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_088 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_088 x y))).fv) 0

theorem nb063_fresh_108 : (nb063_alpha_dummy_010) ∉ (((syn_ccompl (Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_001)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cphi (Class.cv (nb063_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_000)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb063_alpha_dummy_010] using freshVar_not_mem (((syn_ccompl (Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_001)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cphi (Class.cv (nb063_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_000)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb063_fresh_109 (r : Var) (a : Var) : (nb063_alpha_dummy_011 r a) ∉ (((syn_ccompl (Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb063_alpha_dummy_011] using freshVar_not_mem (((syn_ccompl (Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb063_fresh_110 : (nb063_alpha_dummy_046) ∉ (((syn_ccompl (Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cphi (Class.cv (nb063_alpha_dummy_043)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_043))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb063_alpha_dummy_046] using freshVar_not_mem (((syn_ccompl (Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cphi (Class.cv (nb063_alpha_dummy_043)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_042) (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_042)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_043))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb063_fresh_111 (x : Var) (y : Var) : (nb063_alpha_dummy_047 x y) ∉ (((syn_ccompl (Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb063_alpha_dummy_047] using freshVar_not_mem (((syn_ccompl (Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_044 x y) (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb063_fresh_112 : (nb063_alpha_dummy_082) ∉ (((syn_ccompl (Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cphi (Class.cv (nb063_alpha_dummy_079)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_079))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb063_alpha_dummy_082] using freshVar_not_mem (((syn_ccompl (Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_003)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cphi (Class.cv (nb063_alpha_dummy_079)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_078) (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_002)) (Wff.classEq (Class.cv (nb063_alpha_dummy_078)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_079))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb063_fresh_113 (x : Var) (y : Var) : (nb063_alpha_dummy_083 x y) ∉ (((syn_ccompl (Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb063_alpha_dummy_083] using freshVar_not_mem (((syn_ccompl (Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv y) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_080 x y) (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv x) (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb063_fresh_114 : (nb063_alpha_dummy_030) ∉ (((syn_ccompl (Class.cv (nb063_alpha_dummy_021)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_022)))).fv) := by
  simpa only [nb063_alpha_dummy_030] using freshVar_not_mem (((syn_ccompl (Class.cv (nb063_alpha_dummy_021)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_022)))).fv) 0

theorem nb063_fresh_115 (r : Var) (a : Var) : (nb063_alpha_dummy_031 r a) ∉ (((syn_ccompl (Class.cv (nb063_alpha_dummy_024 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_025 r a)))).fv) := by
  simpa only [nb063_alpha_dummy_031] using freshVar_not_mem (((syn_ccompl (Class.cv (nb063_alpha_dummy_024 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_025 r a)))).fv) 0

theorem nb063_fresh_116 : (nb063_alpha_dummy_066) ∉ (((syn_ccompl (Class.cv (nb063_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_058)))).fv) := by
  simpa only [nb063_alpha_dummy_066] using freshVar_not_mem (((syn_ccompl (Class.cv (nb063_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_058)))).fv) 0

theorem nb063_fresh_117 (x : Var) (y : Var) : (nb063_alpha_dummy_067 x y) ∉ (((syn_ccompl (Class.cv (nb063_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_061 x y)))).fv) := by
  simpa only [nb063_alpha_dummy_067] using freshVar_not_mem (((syn_ccompl (Class.cv (nb063_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_061 x y)))).fv) 0

theorem nb063_fresh_118 : (nb063_alpha_dummy_102) ∉ (((syn_ccompl (Class.cv (nb063_alpha_dummy_093)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_094)))).fv) := by
  simpa only [nb063_alpha_dummy_102] using freshVar_not_mem (((syn_ccompl (Class.cv (nb063_alpha_dummy_093)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_094)))).fv) 0

theorem nb063_fresh_119 (x : Var) (y : Var) : (nb063_alpha_dummy_103 x y) ∉ (((syn_ccompl (Class.cv (nb063_alpha_dummy_096 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_097 x y)))).fv) := by
  simpa only [nb063_alpha_dummy_103] using freshVar_not_mem (((syn_ccompl (Class.cv (nb063_alpha_dummy_096 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_097 x y)))).fv) 0

theorem nb063_fresh_120 : (nb063_alpha_dummy_038) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb063_alpha_dummy_038] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb063_fresh_121 (r : Var) (a : Var) : (nb063_alpha_dummy_039 r a) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb063_alpha_dummy_039] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb063_fresh_122 : (nb063_alpha_dummy_074) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_043))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb063_alpha_dummy_074] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_043))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb063_fresh_123 (x : Var) (y : Var) : (nb063_alpha_dummy_075 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb063_alpha_dummy_075] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb063_fresh_124 : (nb063_alpha_dummy_110) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_079))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb063_alpha_dummy_110] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_079))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb063_fresh_125 (x : Var) (y : Var) : (nb063_alpha_dummy_111 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb063_alpha_dummy_111] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb063_fresh_126 : (nb063_alpha_dummy_026) ∉ (((syn_cnin (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022)))).fv) := by
  simpa only [nb063_alpha_dummy_026] using freshVar_not_mem (((syn_cnin (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022)))).fv) 0

theorem nb063_fresh_127 (r : Var) (a : Var) : (nb063_alpha_dummy_027 r a) ∉ (((syn_cnin (Class.cv (nb063_alpha_dummy_024 r a)) (Class.cv (nb063_alpha_dummy_025 r a)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_024 r a)) (Class.cv (nb063_alpha_dummy_025 r a)))).fv) := by
  simpa only [nb063_alpha_dummy_027] using freshVar_not_mem (((syn_cnin (Class.cv (nb063_alpha_dummy_024 r a)) (Class.cv (nb063_alpha_dummy_025 r a)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_024 r a)) (Class.cv (nb063_alpha_dummy_025 r a)))).fv) 0

theorem nb063_fresh_128 : (nb063_alpha_dummy_062) ∉ (((syn_cnin (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058)))).fv) := by
  simpa only [nb063_alpha_dummy_062] using freshVar_not_mem (((syn_cnin (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058)))).fv) 0

theorem nb063_fresh_129 (x : Var) (y : Var) : (nb063_alpha_dummy_063 x y) ∉ (((syn_cnin (Class.cv (nb063_alpha_dummy_060 x y)) (Class.cv (nb063_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_060 x y)) (Class.cv (nb063_alpha_dummy_061 x y)))).fv) := by
  simpa only [nb063_alpha_dummy_063] using freshVar_not_mem (((syn_cnin (Class.cv (nb063_alpha_dummy_060 x y)) (Class.cv (nb063_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_060 x y)) (Class.cv (nb063_alpha_dummy_061 x y)))).fv) 0

theorem nb063_fresh_130 : (nb063_alpha_dummy_098) ∉ (((syn_cnin (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094)))).fv) := by
  simpa only [nb063_alpha_dummy_098] using freshVar_not_mem (((syn_cnin (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094)))).fv) 0

theorem nb063_fresh_131 (x : Var) (y : Var) : (nb063_alpha_dummy_099 x y) ∉ (((syn_cnin (Class.cv (nb063_alpha_dummy_096 x y)) (Class.cv (nb063_alpha_dummy_097 x y)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_096 x y)) (Class.cv (nb063_alpha_dummy_097 x y)))).fv) := by
  simpa only [nb063_alpha_dummy_099] using freshVar_not_mem (((syn_cnin (Class.cv (nb063_alpha_dummy_096 x y)) (Class.cv (nb063_alpha_dummy_097 x y)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_096 x y)) (Class.cv (nb063_alpha_dummy_097 x y)))).fv) 0

theorem nb063_fresh_132 : (nb063_alpha_dummy_040) ∉ (((syn_cphi (Class.cv (nb063_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_007)))).fv) := by
  simpa only [nb063_alpha_dummy_040] using freshVar_not_mem (((syn_cphi (Class.cv (nb063_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_007)))).fv) 0

theorem nb063_fresh_133 (r : Var) (a : Var) : (nb063_alpha_dummy_041 r a) ∉ (((syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))).fv) := by
  simpa only [nb063_alpha_dummy_041] using freshVar_not_mem (((syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))).fv) 0

theorem nb063_fresh_134 : (nb063_alpha_dummy_076) ∉ (((syn_cphi (Class.cv (nb063_alpha_dummy_043)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_043)))).fv) := by
  simpa only [nb063_alpha_dummy_076] using freshVar_not_mem (((syn_cphi (Class.cv (nb063_alpha_dummy_043)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_043)))).fv) 0

theorem nb063_fresh_135 (x : Var) (y : Var) : (nb063_alpha_dummy_077 x y) ∉ (((syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))).fv) := by
  simpa only [nb063_alpha_dummy_077] using freshVar_not_mem (((syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))).fv) 0

theorem nb063_fresh_136 : (nb063_alpha_dummy_112) ∉ (((syn_cphi (Class.cv (nb063_alpha_dummy_079)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_079)))).fv) := by
  simpa only [nb063_alpha_dummy_112] using freshVar_not_mem (((syn_cphi (Class.cv (nb063_alpha_dummy_079)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_079)))).fv) 0

theorem nb063_fresh_137 (x : Var) (y : Var) : (nb063_alpha_dummy_113 x y) ∉ (((syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))).fv) := by
  simpa only [nb063_alpha_dummy_113] using freshVar_not_mem (((syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))).fv ∪ ((syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))).fv) 0

theorem nb063_fresh_138 : (nb063_alpha_dummy_004) ∉ (({(nb063_alpha_dummy_001)} : Finset Var) ∪ ({(nb063_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb063_alpha_dummy_002) (Class.cv (nb063_alpha_dummy_000)) (syn_wral (nb063_alpha_dummy_003) (Class.cv (nb063_alpha_dummy_000)) (syn_wo (syn_wbr (Class.cv (nb063_alpha_dummy_002)) (Class.cv (nb063_alpha_dummy_001)) (Class.cv (nb063_alpha_dummy_003))) (syn_wbr (Class.cv (nb063_alpha_dummy_003)) (Class.cv (nb063_alpha_dummy_001)) (Class.cv (nb063_alpha_dummy_002))))))).fv) := by
  simpa only [nb063_alpha_dummy_004] using freshVar_not_mem (({(nb063_alpha_dummy_001)} : Finset Var) ∪ ({(nb063_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb063_alpha_dummy_002) (Class.cv (nb063_alpha_dummy_000)) (syn_wral (nb063_alpha_dummy_003) (Class.cv (nb063_alpha_dummy_000)) (syn_wo (syn_wbr (Class.cv (nb063_alpha_dummy_002)) (Class.cv (nb063_alpha_dummy_001)) (Class.cv (nb063_alpha_dummy_003))) (syn_wbr (Class.cv (nb063_alpha_dummy_003)) (Class.cv (nb063_alpha_dummy_001)) (Class.cv (nb063_alpha_dummy_002))))))).fv) 0

theorem nb063_fresh_139 (x : Var) (y : Var) (r : Var) (a : Var) : (nb063_alpha_dummy_005 x y r a) ∉ (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wral y (Class.cv a) (syn_wo (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y)) (syn_wbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) := by
  simpa only [nb063_alpha_dummy_005] using freshVar_not_mem (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wral y (Class.cv a) (syn_wo (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y)) (syn_wbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) 0

theorem nb063_fresh_140 : (nb063_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb063_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb063_fresh_141 : (nb063_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb063_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb063_fresh_142 : (nb063_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb063_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb063_fresh_143 : (nb063_alpha_dummy_003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb063_alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb063_distinct_144 : (nb063_alpha_dummy_000) ≠ (nb063_alpha_dummy_001) := by
  simpa only [nb063_alpha_dummy_000, nb063_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb063_distinct_145 : (nb063_alpha_dummy_000) ≠ (nb063_alpha_dummy_002) := by
  simpa only [nb063_alpha_dummy_000, nb063_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb063_distinct_146 : (nb063_alpha_dummy_000) ≠ (nb063_alpha_dummy_003) := by
  simpa only [nb063_alpha_dummy_000, nb063_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb063_distinct_147 : (nb063_alpha_dummy_001) ≠ (nb063_alpha_dummy_002) := by
  simpa only [nb063_alpha_dummy_001, nb063_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb063_distinct_148 : (nb063_alpha_dummy_001) ≠ (nb063_alpha_dummy_003) := by
  simpa only [nb063_alpha_dummy_001, nb063_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb063_distinct_149 : (nb063_alpha_dummy_002) ≠ (nb063_alpha_dummy_003) := by
  simpa only [nb063_alpha_dummy_002, nb063_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb063_support_mem_0000 : (nb063_alpha_dummy_001) ∈ (({(nb063_alpha_dummy_001)} : Finset Var) ∪ ({(nb063_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb063_alpha_dummy_002) (Class.cv (nb063_alpha_dummy_000)) (syn_wral (nb063_alpha_dummy_003) (Class.cv (nb063_alpha_dummy_000)) (syn_wo (syn_wbr (Class.cv (nb063_alpha_dummy_002)) (Class.cv (nb063_alpha_dummy_001)) (Class.cv (nb063_alpha_dummy_003))) (syn_wbr (Class.cv (nb063_alpha_dummy_003)) (Class.cv (nb063_alpha_dummy_001)) (Class.cv (nb063_alpha_dummy_002))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0001 (x : Var) (y : Var) (r : Var) (a : Var) : r ∈ (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wral y (Class.cv a) (syn_wo (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y)) (syn_wbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0002 : (nb063_alpha_dummy_000) ∈ (({(nb063_alpha_dummy_001)} : Finset Var) ∪ ({(nb063_alpha_dummy_000)} : Finset Var) ∪ ((syn_wral (nb063_alpha_dummy_002) (Class.cv (nb063_alpha_dummy_000)) (syn_wral (nb063_alpha_dummy_003) (Class.cv (nb063_alpha_dummy_000)) (syn_wo (syn_wbr (Class.cv (nb063_alpha_dummy_002)) (Class.cv (nb063_alpha_dummy_001)) (Class.cv (nb063_alpha_dummy_003))) (syn_wbr (Class.cv (nb063_alpha_dummy_003)) (Class.cv (nb063_alpha_dummy_001)) (Class.cv (nb063_alpha_dummy_002))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0003 (x : Var) (y : Var) (r : Var) (a : Var) : a ∈ (({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wral x (Class.cv a) (syn_wral y (Class.cv a) (syn_wo (syn_wbr (Class.cv x) (Class.cv r) (Class.cv y)) (syn_wbr (Class.cv y) (Class.cv r) (Class.cv x)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0004 : (nb063_alpha_dummy_001) ∈ (((Class.cv (nb063_alpha_dummy_001))).fv ∪ ((Class.cv (nb063_alpha_dummy_000))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0005 : (nb063_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_001)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cphi (Class.cv (nb063_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_000)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0006 (r : Var) (a : Var) : r ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0007 (r : Var) (a : Var) : r ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0006 r a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0006 r a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0008 : (nb063_alpha_dummy_001) ∈ (((Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_001)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cphi (Class.cv (nb063_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_001)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cphi (Class.cv (nb063_alpha_dummy_007))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0009 (r : Var) (a : Var) : r ∈ (((Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))))))).fv ∪ ((Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0006 r a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0006 r a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0010 : (nb063_alpha_dummy_007) ∈ (((Class.cv (nb063_alpha_dummy_007))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0011 (r : Var) (a : Var) : (nb063_alpha_dummy_009 r a) ∈ (((Class.cv (nb063_alpha_dummy_009 r a))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0012 : (nb063_alpha_dummy_014) ∈ (((Wff.classMem (Class.cv (nb063_alpha_dummy_014)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_014)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_014))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0013 (r : Var) (a : Var) : (nb063_alpha_dummy_016 r a) ∈ (((Wff.classMem (Class.cv (nb063_alpha_dummy_016 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb063_alpha_dummy_016 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb063_alpha_dummy_016 r a))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0014 : (nb063_alpha_dummy_014) ∈ (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0015 (r : Var) (a : Var) : (nb063_alpha_dummy_016 r a) ∈ (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0016 : (nb063_alpha_dummy_021) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0017 (r : Var) (a : Var) : (nb063_alpha_dummy_024 r a) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_024 r a)) (Class.cv (nb063_alpha_dummy_025 r a)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_024 r a)) (Class.cv (nb063_alpha_dummy_025 r a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0018 : (nb063_alpha_dummy_021) ∈ (((Class.cv (nb063_alpha_dummy_021))).fv ∪ ((Class.cv (nb063_alpha_dummy_022))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0019 (r : Var) (a : Var) : (nb063_alpha_dummy_024 r a) ∈ (((Class.cv (nb063_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb063_alpha_dummy_025 r a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0020 : (nb063_alpha_dummy_022) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0021 (r : Var) (a : Var) : (nb063_alpha_dummy_025 r a) ∈ (((syn_cnin (Class.cv (nb063_alpha_dummy_024 r a)) (Class.cv (nb063_alpha_dummy_025 r a)))).fv ∪ ((syn_cnin (Class.cv (nb063_alpha_dummy_024 r a)) (Class.cv (nb063_alpha_dummy_025 r a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0022 : (nb063_alpha_dummy_022) ∈ (((Class.cv (nb063_alpha_dummy_021))).fv ∪ ((Class.cv (nb063_alpha_dummy_022))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0023 (r : Var) (a : Var) : (nb063_alpha_dummy_025 r a) ∈ (((Class.cv (nb063_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb063_alpha_dummy_025 r a))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0024 : (nb063_alpha_dummy_021) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_021)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_022)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0025 (r : Var) (a : Var) : (nb063_alpha_dummy_024 r a) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_024 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_025 r a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0026 : (nb063_alpha_dummy_021) ∈ (((Class.cv (nb063_alpha_dummy_021))).fv ∪ ((Class.cv (nb063_alpha_dummy_021))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0027 (r : Var) (a : Var) : (nb063_alpha_dummy_024 r a) ∈ (((Class.cv (nb063_alpha_dummy_024 r a))).fv ∪ ((Class.cv (nb063_alpha_dummy_024 r a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0028 : (nb063_alpha_dummy_022) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_021)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_022)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0029 (r : Var) (a : Var) : (nb063_alpha_dummy_025 r a) ∈ (((syn_ccompl (Class.cv (nb063_alpha_dummy_024 r a)))).fv ∪ ((syn_ccompl (Class.cv (nb063_alpha_dummy_025 r a)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0030 : (nb063_alpha_dummy_022) ∈ (((Class.cv (nb063_alpha_dummy_022))).fv ∪ ((Class.cv (nb063_alpha_dummy_022))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0031 (r : Var) (a : Var) : (nb063_alpha_dummy_025 r a) ∈ (((Class.cv (nb063_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb063_alpha_dummy_025 r a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0032 : (nb063_alpha_dummy_000) ∈ (((Class.cv (nb063_alpha_dummy_001))).fv ∪ ((Class.cv (nb063_alpha_dummy_000))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0033 : (nb063_alpha_dummy_000) ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_001)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cphi (Class.cv (nb063_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_006) (syn_wrex (nb063_alpha_dummy_007) (Class.cv (nb063_alpha_dummy_000)) (Wff.classEq (Class.cv (nb063_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb063_support_mem_0034 (r : Var) (a : Var) : a ∈ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb063_support_mem_0035 (r : Var) (a : Var) : a ∈ (((syn_ccompl (Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv r) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb063_alpha_dummy_008 r a) (syn_wrex (nb063_alpha_dummy_009 r a) (Class.cv a) (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a)) (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0034 r a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0034 r a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
