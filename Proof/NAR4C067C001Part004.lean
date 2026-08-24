import NAR4C067C001Part003

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

theorem nb067_fresh_071 (x : Var) (y : Var) : (nb067_alpha_dummy_034 x y) ∉ (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_072 (x : Var) (y : Var) : (nb067_alpha_dummy_032 x y) ≠ (nb067_alpha_dummy_033 x y) := by
  simpa only [nb067_alpha_dummy_032, nb067_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_073 (x : Var) (y : Var) : (nb067_alpha_dummy_032 x y) ≠ (nb067_alpha_dummy_034 x y) := by
  simpa only [nb067_alpha_dummy_032, nb067_alpha_dummy_034] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_074 (x : Var) (y : Var) : (nb067_alpha_dummy_033 x y) ≠ (nb067_alpha_dummy_034 x y) := by
  simpa only [nb067_alpha_dummy_033, nb067_alpha_dummy_034] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_075 : (nb067_alpha_dummy_041) ∉ (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_030))).fv) := by
  simpa only [nb067_alpha_dummy_041] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_030))).fv) 0

theorem nb067_fresh_076 : (nb067_alpha_dummy_037) ∉ (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) := by
  simpa only [nb067_alpha_dummy_037] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) 0

theorem nb067_fresh_077 : (nb067_alpha_dummy_043) ∉ (((Class.cv (nb067_alpha_dummy_031))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) := by
  simpa only [nb067_alpha_dummy_043] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_031))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) 0

theorem nb067_fresh_078 (x : Var) (y : Var) : (nb067_alpha_dummy_042 x y) ∉ (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_033 x y))).fv) := by
  simpa only [nb067_alpha_dummy_042] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_033 x y))).fv) 0

theorem nb067_fresh_079 (x : Var) (y : Var) : (nb067_alpha_dummy_038 x y) ∉ (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_034 x y))).fv) := by
  simpa only [nb067_alpha_dummy_038] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_034 x y))).fv) 0

theorem nb067_fresh_080 (x : Var) (y : Var) : (nb067_alpha_dummy_044 x y) ∉ (((Class.cv (nb067_alpha_dummy_034 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_034 x y))).fv) := by
  simpa only [nb067_alpha_dummy_044] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_034 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_034 x y))).fv) 0

theorem nb067_fresh_081 : (nb067_alpha_dummy_057) ∉ (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_057] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_082 : (nb067_alpha_dummy_058) ∉ (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_058] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_083 : (nb067_alpha_dummy_059) ∉ (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_084 : (nb067_alpha_dummy_057) ≠ (nb067_alpha_dummy_058) := by
  simpa only [nb067_alpha_dummy_057, nb067_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_085 : (nb067_alpha_dummy_057) ≠ (nb067_alpha_dummy_059) := by
  simpa only [nb067_alpha_dummy_057, nb067_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_086 : (nb067_alpha_dummy_058) ≠ (nb067_alpha_dummy_059) := by
  simpa only [nb067_alpha_dummy_058, nb067_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_087 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_060 x y f) ∉ (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_088 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_061 x y f) ∉ (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_089 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_062 x y f) ∉ (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_090 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_060 x y f) ≠ (nb067_alpha_dummy_061 x y f) := by
  simpa only [nb067_alpha_dummy_060, nb067_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_091 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_060 x y f) ≠ (nb067_alpha_dummy_062 x y f) := by
  simpa only [nb067_alpha_dummy_060, nb067_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_092 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_061 x y f) ≠ (nb067_alpha_dummy_062 x y f) := by
  simpa only [nb067_alpha_dummy_061, nb067_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_093 : (nb067_alpha_dummy_069) ∉ (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_058))).fv) := by
  simpa only [nb067_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_058))).fv) 0

theorem nb067_fresh_094 : (nb067_alpha_dummy_065) ∉ (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) := by
  simpa only [nb067_alpha_dummy_065] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_058))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) 0

theorem nb067_fresh_095 : (nb067_alpha_dummy_071) ∉ (((Class.cv (nb067_alpha_dummy_059))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) := by
  simpa only [nb067_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_059))).fv ∪ ((Class.cv (nb067_alpha_dummy_059))).fv) 0

theorem nb067_fresh_096 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_070 x y f) ∉ (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_061 x y f))).fv) := by
  simpa only [nb067_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_061 x y f))).fv) 0

theorem nb067_fresh_097 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_066 x y f) ∉ (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) := by
  simpa only [nb067_alpha_dummy_066] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_061 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) 0

theorem nb067_fresh_098 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_072 x y f) ∉ (((Class.cv (nb067_alpha_dummy_062 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) := by
  simpa only [nb067_alpha_dummy_072] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_062 x y f))).fv ∪ ((Class.cv (nb067_alpha_dummy_062 x y f))).fv) 0

theorem nb067_fresh_099 : (nb067_alpha_dummy_091) ∉ (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) := by
  simpa only [nb067_alpha_dummy_091] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 0

theorem nb067_fresh_100 : (nb067_alpha_dummy_092) ∉ (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) := by
  simpa only [nb067_alpha_dummy_092] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 1

theorem nb067_distinct_101 : (nb067_alpha_dummy_091) ≠ (nb067_alpha_dummy_092) := by
  simpa only [nb067_alpha_dummy_091, nb067_alpha_dummy_092] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_102 : (nb067_alpha_dummy_127) ∉ (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) := by
  simpa only [nb067_alpha_dummy_127] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) 0

theorem nb067_fresh_103 : (nb067_alpha_dummy_128) ∉ (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) := by
  simpa only [nb067_alpha_dummy_128] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) 1

theorem nb067_distinct_104 : (nb067_alpha_dummy_127) ≠ (nb067_alpha_dummy_128) := by
  simpa only [nb067_alpha_dummy_127, nb067_alpha_dummy_128] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪ ((Class.cv (nb067_alpha_dummy_085))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_105 : (nb067_alpha_dummy_241) ∉ (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) := by
  simpa only [nb067_alpha_dummy_241] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 0

theorem nb067_fresh_106 : (nb067_alpha_dummy_242) ∉ (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) := by
  simpa only [nb067_alpha_dummy_242] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) 1

theorem nb067_distinct_107 : (nb067_alpha_dummy_241) ≠ (nb067_alpha_dummy_242) := by
  simpa only [nb067_alpha_dummy_241, nb067_alpha_dummy_242] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_085))).fv ∪ ((Class.cv (nb067_alpha_dummy_084))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_108 (f : Var) : (nb067_alpha_dummy_093 f) ∉ (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) := by
  simpa only [nb067_alpha_dummy_093] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) 0

theorem nb067_fresh_109 (f : Var) : (nb067_alpha_dummy_094 f) ∉ (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) := by
  simpa only [nb067_alpha_dummy_094] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) 1

theorem nb067_distinct_110 (f : Var) : (nb067_alpha_dummy_093 f) ≠ (nb067_alpha_dummy_094 f) := by
  simpa only [nb067_alpha_dummy_093, nb067_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_111 (f : Var) : (nb067_alpha_dummy_129 f) ∉ (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) := by
  simpa only [nb067_alpha_dummy_129] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) 0

theorem nb067_fresh_112 (f : Var) : (nb067_alpha_dummy_130 f) ∉ (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) := by
  simpa only [nb067_alpha_dummy_130] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) 1

theorem nb067_distinct_113 (f : Var) : (nb067_alpha_dummy_129 f) ≠ (nb067_alpha_dummy_130 f) := by
  simpa only [nb067_alpha_dummy_129, nb067_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_088 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_114 (f : Var) : (nb067_alpha_dummy_243 f) ∉ (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) := by
  simpa only [nb067_alpha_dummy_243] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) 0

theorem nb067_fresh_115 (f : Var) : (nb067_alpha_dummy_244 f) ∉ (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) := by
  simpa only [nb067_alpha_dummy_244] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) 1

theorem nb067_distinct_116 (f : Var) : (nb067_alpha_dummy_243 f) ≠ (nb067_alpha_dummy_244 f) := by
  simpa only [nb067_alpha_dummy_243, nb067_alpha_dummy_244] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_087 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_117 : (nb067_alpha_dummy_099) ∉ (((Class.cv (nb067_alpha_dummy_092))).fv) := by
  simpa only [nb067_alpha_dummy_099] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_092))).fv) 0

theorem nb067_fresh_118 : (nb067_alpha_dummy_100) ∉ (((Class.cv (nb067_alpha_dummy_092))).fv) := by
  simpa only [nb067_alpha_dummy_100] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_092))).fv) 1

theorem nb067_distinct_119 : (nb067_alpha_dummy_099) ≠ (nb067_alpha_dummy_100) := by
  simpa only [nb067_alpha_dummy_099, nb067_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_092))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_120 (f : Var) : (nb067_alpha_dummy_101 f) ∉ (((Class.cv (nb067_alpha_dummy_094 f))).fv) := by
  simpa only [nb067_alpha_dummy_101] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_094 f))).fv) 0

theorem nb067_fresh_121 (f : Var) : (nb067_alpha_dummy_102 f) ∉ (((Class.cv (nb067_alpha_dummy_094 f))).fv) := by
  simpa only [nb067_alpha_dummy_102] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_094 f))).fv) 1

theorem nb067_distinct_122 (f : Var) : (nb067_alpha_dummy_101 f) ≠ (nb067_alpha_dummy_102 f) := by
  simpa only [nb067_alpha_dummy_101, nb067_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_094 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_123 : (nb067_alpha_dummy_105) ∉ (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_105] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_124 : (nb067_alpha_dummy_106) ∉ (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_106] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_125 : (nb067_alpha_dummy_107) ∉ (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_107] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_126 : (nb067_alpha_dummy_105) ≠ (nb067_alpha_dummy_106) := by
  simpa only [nb067_alpha_dummy_105, nb067_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_127 : (nb067_alpha_dummy_105) ≠ (nb067_alpha_dummy_107) := by
  simpa only [nb067_alpha_dummy_105, nb067_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_128 : (nb067_alpha_dummy_106) ≠ (nb067_alpha_dummy_107) := by
  simpa only [nb067_alpha_dummy_106, nb067_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_129 (f : Var) : (nb067_alpha_dummy_108 f) ∉ (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_108] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_130 (f : Var) : (nb067_alpha_dummy_109 f) ∉ (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_109] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_131 (f : Var) : (nb067_alpha_dummy_110 f) ∉ (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_110] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_132 (f : Var) : (nb067_alpha_dummy_108 f) ≠ (nb067_alpha_dummy_109 f) := by
  simpa only [nb067_alpha_dummy_108, nb067_alpha_dummy_109] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_133 (f : Var) : (nb067_alpha_dummy_108 f) ≠ (nb067_alpha_dummy_110 f) := by
  simpa only [nb067_alpha_dummy_108, nb067_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_134 (f : Var) : (nb067_alpha_dummy_109 f) ≠ (nb067_alpha_dummy_110 f) := by
  simpa only [nb067_alpha_dummy_109, nb067_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_135 : (nb067_alpha_dummy_117) ∉ (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_106))).fv) := by
  simpa only [nb067_alpha_dummy_117] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_106))).fv) 0

theorem nb067_fresh_136 : (nb067_alpha_dummy_113) ∉ (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) := by
  simpa only [nb067_alpha_dummy_113] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_106))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) 0

theorem nb067_fresh_137 : (nb067_alpha_dummy_119) ∉ (((Class.cv (nb067_alpha_dummy_107))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) := by
  simpa only [nb067_alpha_dummy_119] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_107))).fv ∪ ((Class.cv (nb067_alpha_dummy_107))).fv) 0

theorem nb067_fresh_138 (f : Var) : (nb067_alpha_dummy_118 f) ∉ (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_109 f))).fv) := by
  simpa only [nb067_alpha_dummy_118] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_109 f))).fv) 0

theorem nb067_fresh_139 (f : Var) : (nb067_alpha_dummy_114 f) ∉ (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) := by
  simpa only [nb067_alpha_dummy_114] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) 0

theorem nb067_fresh_140 (f : Var) : (nb067_alpha_dummy_120 f) ∉ (((Class.cv (nb067_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) := by
  simpa only [nb067_alpha_dummy_120] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_110 f))).fv) 0

theorem nb067_fresh_141 : (nb067_alpha_dummy_135) ∉ (((Class.cv (nb067_alpha_dummy_128))).fv) := by
  simpa only [nb067_alpha_dummy_135] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_128))).fv) 0

theorem nb067_fresh_142 : (nb067_alpha_dummy_136) ∉ (((Class.cv (nb067_alpha_dummy_128))).fv) := by
  simpa only [nb067_alpha_dummy_136] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_128))).fv) 1

theorem nb067_distinct_143 : (nb067_alpha_dummy_135) ≠ (nb067_alpha_dummy_136) := by
  simpa only [nb067_alpha_dummy_135, nb067_alpha_dummy_136] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_128))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_144 (f : Var) : (nb067_alpha_dummy_137 f) ∉ (((Class.cv (nb067_alpha_dummy_130 f))).fv) := by
  simpa only [nb067_alpha_dummy_137] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_130 f))).fv) 0

theorem nb067_fresh_145 (f : Var) : (nb067_alpha_dummy_138 f) ∉ (((Class.cv (nb067_alpha_dummy_130 f))).fv) := by
  simpa only [nb067_alpha_dummy_138] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_130 f))).fv) 1

theorem nb067_distinct_146 (f : Var) : (nb067_alpha_dummy_137 f) ≠ (nb067_alpha_dummy_138 f) := by
  simpa only [nb067_alpha_dummy_137, nb067_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_130 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_147 : (nb067_alpha_dummy_141) ∉ (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_141] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_148 : (nb067_alpha_dummy_142) ∉ (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_142] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_149 : (nb067_alpha_dummy_143) ∉ (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_143] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_150 : (nb067_alpha_dummy_141) ≠ (nb067_alpha_dummy_142) := by
  simpa only [nb067_alpha_dummy_141, nb067_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_151 : (nb067_alpha_dummy_141) ≠ (nb067_alpha_dummy_143) := by
  simpa only [nb067_alpha_dummy_141, nb067_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_152 : (nb067_alpha_dummy_142) ≠ (nb067_alpha_dummy_143) := by
  simpa only [nb067_alpha_dummy_142, nb067_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_153 (f : Var) : (nb067_alpha_dummy_144 f) ∉ (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_144] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_154 (f : Var) : (nb067_alpha_dummy_145 f) ∉ (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_145] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_155 (f : Var) : (nb067_alpha_dummy_146 f) ∉ (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_146] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_156 (f : Var) : (nb067_alpha_dummy_144 f) ≠ (nb067_alpha_dummy_145 f) := by
  simpa only [nb067_alpha_dummy_144, nb067_alpha_dummy_145] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_157 (f : Var) : (nb067_alpha_dummy_144 f) ≠ (nb067_alpha_dummy_146 f) := by
  simpa only [nb067_alpha_dummy_144, nb067_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_158 (f : Var) : (nb067_alpha_dummy_145 f) ≠ (nb067_alpha_dummy_146 f) := by
  simpa only [nb067_alpha_dummy_145, nb067_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_159 : (nb067_alpha_dummy_153) ∉ (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_142))).fv) := by
  simpa only [nb067_alpha_dummy_153] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_142))).fv) 0

theorem nb067_fresh_160 : (nb067_alpha_dummy_149) ∉ (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) := by
  simpa only [nb067_alpha_dummy_149] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_142))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) 0

theorem nb067_fresh_161 : (nb067_alpha_dummy_155) ∉ (((Class.cv (nb067_alpha_dummy_143))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) := by
  simpa only [nb067_alpha_dummy_155] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_143))).fv ∪ ((Class.cv (nb067_alpha_dummy_143))).fv) 0

theorem nb067_fresh_162 (f : Var) : (nb067_alpha_dummy_154 f) ∉ (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_145 f))).fv) := by
  simpa only [nb067_alpha_dummy_154] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_145 f))).fv) 0

theorem nb067_fresh_163 (f : Var) : (nb067_alpha_dummy_150 f) ∉ (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) := by
  simpa only [nb067_alpha_dummy_150] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) 0

theorem nb067_fresh_164 (f : Var) : (nb067_alpha_dummy_156 f) ∉ (((Class.cv (nb067_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) := by
  simpa only [nb067_alpha_dummy_156] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_146 f))).fv) 0

theorem nb067_fresh_165 : (nb067_alpha_dummy_169) ∉ (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) := by
  simpa only [nb067_alpha_dummy_169] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) 0

theorem nb067_fresh_166 : (nb067_alpha_dummy_170) ∉ (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) := by
  simpa only [nb067_alpha_dummy_170] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) 1

theorem nb067_distinct_167 : (nb067_alpha_dummy_169) ≠ (nb067_alpha_dummy_170) := by
  simpa only [nb067_alpha_dummy_169, nb067_alpha_dummy_170] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_163))).fv ∪ ((Class.cv (nb067_alpha_dummy_164))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_168 : (nb067_alpha_dummy_205) ∉ (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) := by
  simpa only [nb067_alpha_dummy_205] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) 0

theorem nb067_fresh_169 : (nb067_alpha_dummy_206) ∉ (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) := by
  simpa only [nb067_alpha_dummy_206] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) 1

theorem nb067_distinct_170 : (nb067_alpha_dummy_205) ≠ (nb067_alpha_dummy_206) := by
  simpa only [nb067_alpha_dummy_205, nb067_alpha_dummy_206] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_164))).fv ∪ ((Class.cv (nb067_alpha_dummy_163))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_171 (f : Var) : (nb067_alpha_dummy_171 f) ∉ (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) := by
  simpa only [nb067_alpha_dummy_171] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) 0

theorem nb067_fresh_172 (f : Var) : (nb067_alpha_dummy_172 f) ∉ (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) := by
  simpa only [nb067_alpha_dummy_172] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) 1

theorem nb067_distinct_173 (f : Var) : (nb067_alpha_dummy_171 f) ≠ (nb067_alpha_dummy_172 f) := by
  simpa only [nb067_alpha_dummy_171, nb067_alpha_dummy_172] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_166 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_174 (f : Var) : (nb067_alpha_dummy_207 f) ∉ (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) := by
  simpa only [nb067_alpha_dummy_207] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) 0

theorem nb067_fresh_175 (f : Var) : (nb067_alpha_dummy_208 f) ∉ (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) := by
  simpa only [nb067_alpha_dummy_208] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) 1

theorem nb067_distinct_176 (f : Var) : (nb067_alpha_dummy_207 f) ≠ (nb067_alpha_dummy_208 f) := by
  simpa only [nb067_alpha_dummy_207, nb067_alpha_dummy_208] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_165 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_177 : (nb067_alpha_dummy_177) ∉ (((Class.cv (nb067_alpha_dummy_170))).fv) := by
  simpa only [nb067_alpha_dummy_177] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_170))).fv) 0

theorem nb067_fresh_178 : (nb067_alpha_dummy_178) ∉ (((Class.cv (nb067_alpha_dummy_170))).fv) := by
  simpa only [nb067_alpha_dummy_178] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_170))).fv) 1

theorem nb067_distinct_179 : (nb067_alpha_dummy_177) ≠ (nb067_alpha_dummy_178) := by
  simpa only [nb067_alpha_dummy_177, nb067_alpha_dummy_178] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_180 (f : Var) : (nb067_alpha_dummy_179 f) ∉ (((Class.cv (nb067_alpha_dummy_172 f))).fv) := by
  simpa only [nb067_alpha_dummy_179] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_172 f))).fv) 0

theorem nb067_fresh_181 (f : Var) : (nb067_alpha_dummy_180 f) ∉ (((Class.cv (nb067_alpha_dummy_172 f))).fv) := by
  simpa only [nb067_alpha_dummy_180] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_172 f))).fv) 1

theorem nb067_distinct_182 (f : Var) : (nb067_alpha_dummy_179 f) ≠ (nb067_alpha_dummy_180 f) := by
  simpa only [nb067_alpha_dummy_179, nb067_alpha_dummy_180] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_183 : (nb067_alpha_dummy_183) ∉ (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_183] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_184 : (nb067_alpha_dummy_184) ∉ (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_184] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_185 : (nb067_alpha_dummy_185) ∉ (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_185] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_186 : (nb067_alpha_dummy_183) ≠ (nb067_alpha_dummy_184) := by
  simpa only [nb067_alpha_dummy_183, nb067_alpha_dummy_184] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_187 : (nb067_alpha_dummy_183) ≠ (nb067_alpha_dummy_185) := by
  simpa only [nb067_alpha_dummy_183, nb067_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_188 : (nb067_alpha_dummy_184) ≠ (nb067_alpha_dummy_185) := by
  simpa only [nb067_alpha_dummy_184, nb067_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_189 (f : Var) : (nb067_alpha_dummy_186 f) ∉ (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_186] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_190 (f : Var) : (nb067_alpha_dummy_187 f) ∉ (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_187] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_191 (f : Var) : (nb067_alpha_dummy_188 f) ∉ (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_188] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_192 (f : Var) : (nb067_alpha_dummy_186 f) ≠ (nb067_alpha_dummy_187 f) := by
  simpa only [nb067_alpha_dummy_186, nb067_alpha_dummy_187] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_193 (f : Var) : (nb067_alpha_dummy_186 f) ≠ (nb067_alpha_dummy_188 f) := by
  simpa only [nb067_alpha_dummy_186, nb067_alpha_dummy_188] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_194 (f : Var) : (nb067_alpha_dummy_187 f) ≠ (nb067_alpha_dummy_188 f) := by
  simpa only [nb067_alpha_dummy_187, nb067_alpha_dummy_188] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_195 : (nb067_alpha_dummy_195) ∉ (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_184))).fv) := by
  simpa only [nb067_alpha_dummy_195] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_184))).fv) 0

theorem nb067_fresh_196 : (nb067_alpha_dummy_191) ∉ (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) := by
  simpa only [nb067_alpha_dummy_191] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_184))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) 0

theorem nb067_fresh_197 : (nb067_alpha_dummy_197) ∉ (((Class.cv (nb067_alpha_dummy_185))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) := by
  simpa only [nb067_alpha_dummy_197] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_185))).fv ∪ ((Class.cv (nb067_alpha_dummy_185))).fv) 0

theorem nb067_fresh_198 (f : Var) : (nb067_alpha_dummy_196 f) ∉ (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_187 f))).fv) := by
  simpa only [nb067_alpha_dummy_196] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_187 f))).fv) 0

theorem nb067_fresh_199 (f : Var) : (nb067_alpha_dummy_192 f) ∉ (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) := by
  simpa only [nb067_alpha_dummy_192] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_187 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) 0

theorem nb067_fresh_200 (f : Var) : (nb067_alpha_dummy_198 f) ∉ (((Class.cv (nb067_alpha_dummy_188 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) := by
  simpa only [nb067_alpha_dummy_198] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_188 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_188 f))).fv) 0

theorem nb067_fresh_201 : (nb067_alpha_dummy_213) ∉ (((Class.cv (nb067_alpha_dummy_206))).fv) := by
  simpa only [nb067_alpha_dummy_213] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_206))).fv) 0

theorem nb067_fresh_202 : (nb067_alpha_dummy_214) ∉ (((Class.cv (nb067_alpha_dummy_206))).fv) := by
  simpa only [nb067_alpha_dummy_214] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_206))).fv) 1

theorem nb067_distinct_203 : (nb067_alpha_dummy_213) ≠ (nb067_alpha_dummy_214) := by
  simpa only [nb067_alpha_dummy_213, nb067_alpha_dummy_214] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_206))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_204 (f : Var) : (nb067_alpha_dummy_215 f) ∉ (((Class.cv (nb067_alpha_dummy_208 f))).fv) := by
  simpa only [nb067_alpha_dummy_215] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_208 f))).fv) 0

theorem nb067_fresh_205 (f : Var) : (nb067_alpha_dummy_216 f) ∉ (((Class.cv (nb067_alpha_dummy_208 f))).fv) := by
  simpa only [nb067_alpha_dummy_216] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_208 f))).fv) 1

theorem nb067_distinct_206 (f : Var) : (nb067_alpha_dummy_215 f) ≠ (nb067_alpha_dummy_216 f) := by
  simpa only [nb067_alpha_dummy_215, nb067_alpha_dummy_216] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_208 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_207 : (nb067_alpha_dummy_219) ∉ (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_219] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_208 : (nb067_alpha_dummy_220) ∉ (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_220] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_209 : (nb067_alpha_dummy_221) ∉ (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_221] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_210 : (nb067_alpha_dummy_219) ≠ (nb067_alpha_dummy_220) := by
  simpa only [nb067_alpha_dummy_219, nb067_alpha_dummy_220] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_211 : (nb067_alpha_dummy_219) ≠ (nb067_alpha_dummy_221) := by
  simpa only [nb067_alpha_dummy_219, nb067_alpha_dummy_221] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_212 : (nb067_alpha_dummy_220) ≠ (nb067_alpha_dummy_221) := by
  simpa only [nb067_alpha_dummy_220, nb067_alpha_dummy_221] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_213 (f : Var) : (nb067_alpha_dummy_222 f) ∉ (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_222] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_214 (f : Var) : (nb067_alpha_dummy_223 f) ∉ (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_223] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_215 (f : Var) : (nb067_alpha_dummy_224 f) ∉ (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_224] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_216 (f : Var) : (nb067_alpha_dummy_222 f) ≠ (nb067_alpha_dummy_223 f) := by
  simpa only [nb067_alpha_dummy_222, nb067_alpha_dummy_223] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_217 (f : Var) : (nb067_alpha_dummy_222 f) ≠ (nb067_alpha_dummy_224 f) := by
  simpa only [nb067_alpha_dummy_222, nb067_alpha_dummy_224] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_218 (f : Var) : (nb067_alpha_dummy_223 f) ≠ (nb067_alpha_dummy_224 f) := by
  simpa only [nb067_alpha_dummy_223, nb067_alpha_dummy_224] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_219 : (nb067_alpha_dummy_231) ∉ (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_220))).fv) := by
  simpa only [nb067_alpha_dummy_231] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_220))).fv) 0

theorem nb067_fresh_220 : (nb067_alpha_dummy_227) ∉ (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) := by
  simpa only [nb067_alpha_dummy_227] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_220))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
