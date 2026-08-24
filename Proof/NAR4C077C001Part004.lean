import NAR4C077C001Part003

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

theorem nb077_distinct_069 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_036 x F I) ≠ (nb077_alpha_dummy_038 x F I) := by
  simpa only [nb077_alpha_dummy_036, nb077_alpha_dummy_038] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_070 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_038 x F I) := by
  simpa only [nb077_alpha_dummy_037, nb077_alpha_dummy_038] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_071 (F : Class) (I : Class) : (nb077_alpha_dummy_045 F I) ∉ (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_034 F I))).fv) := by
  simpa only [nb077_alpha_dummy_045] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_034 F I))).fv) 0

theorem nb077_fresh_072 (F : Class) (I : Class) : (nb077_alpha_dummy_041 F I) ∉ (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_035 F I))).fv) := by
  simpa only [nb077_alpha_dummy_041] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_035 F I))).fv) 0

theorem nb077_fresh_073 (F : Class) (I : Class) : (nb077_alpha_dummy_047 F I) ∉ (((Class.cv (nb077_alpha_dummy_035 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_035 F I))).fv) := by
  simpa only [nb077_alpha_dummy_047] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_035 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_035 F I))).fv) 0

theorem nb077_fresh_074 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_046 x F I) ∉ (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_037 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_046] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_037 x F I))).fv) 0

theorem nb077_fresh_075 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_042 x F I) ∉ (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_042] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) 0

theorem nb077_fresh_076 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_048 x F I) ∉ (((Class.cv (nb077_alpha_dummy_038 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_048] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_038 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) 0

theorem nb077_fresh_077 (F : Class) (I : Class) : (nb077_alpha_dummy_067 F I) ∉ (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) := by
  simpa only [nb077_alpha_dummy_067] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 0

theorem nb077_fresh_078 (F : Class) (I : Class) : (nb077_alpha_dummy_068 F I) ∉ (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) := by
  simpa only [nb077_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 1

theorem nb077_distinct_079 (F : Class) (I : Class) : (nb077_alpha_dummy_067 F I) ≠ (nb077_alpha_dummy_068 F I) := by
  simpa only [nb077_alpha_dummy_067, nb077_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_080 (F : Class) (I : Class) : (nb077_alpha_dummy_103 F I) ∉ (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_061 F I))).fv) := by
  simpa only [nb077_alpha_dummy_103] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_061 F I))).fv) 0

theorem nb077_fresh_081 (F : Class) (I : Class) : (nb077_alpha_dummy_104 F I) ∉ (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_061 F I))).fv) := by
  simpa only [nb077_alpha_dummy_104] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_061 F I))).fv) 1

theorem nb077_distinct_082 (F : Class) (I : Class) : (nb077_alpha_dummy_103 F I) ≠ (nb077_alpha_dummy_104 F I) := by
  simpa only [nb077_alpha_dummy_103, nb077_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_059 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_061 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_083 (F : Class) (I : Class) : (nb077_alpha_dummy_311 F I) ∉ (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) := by
  simpa only [nb077_alpha_dummy_311] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 0

theorem nb077_fresh_084 (F : Class) (I : Class) : (nb077_alpha_dummy_312 F I) ∉ (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) := by
  simpa only [nb077_alpha_dummy_312] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 1

theorem nb077_distinct_085 (F : Class) (I : Class) : (nb077_alpha_dummy_311 F I) ≠ (nb077_alpha_dummy_312 F I) := by
  simpa only [nb077_alpha_dummy_311, nb077_alpha_dummy_312] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_086 (x : Var) : (nb077_alpha_dummy_069 x) ∉ (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) := by
  simpa only [nb077_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) 0

theorem nb077_fresh_087 (x : Var) : (nb077_alpha_dummy_070 x) ∉ (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) := by
  simpa only [nb077_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) 1

theorem nb077_distinct_088 (x : Var) : (nb077_alpha_dummy_069 x) ≠ (nb077_alpha_dummy_070 x) := by
  simpa only [nb077_alpha_dummy_069, nb077_alpha_dummy_070] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_089 (x : Var) : (nb077_alpha_dummy_105 x) ∉ (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) := by
  simpa only [nb077_alpha_dummy_105] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) 0

theorem nb077_fresh_090 (x : Var) : (nb077_alpha_dummy_106 x) ∉ (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) := by
  simpa only [nb077_alpha_dummy_106] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) 1

theorem nb077_distinct_091 (x : Var) : (nb077_alpha_dummy_105 x) ≠ (nb077_alpha_dummy_106 x) := by
  simpa only [nb077_alpha_dummy_105, nb077_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_062 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_064 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_092 (x : Var) : (nb077_alpha_dummy_313 x) ∉ (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) := by
  simpa only [nb077_alpha_dummy_313] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) 0

theorem nb077_fresh_093 (x : Var) : (nb077_alpha_dummy_314 x) ∉ (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) := by
  simpa only [nb077_alpha_dummy_314] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) 1

theorem nb077_distinct_094 (x : Var) : (nb077_alpha_dummy_313 x) ≠ (nb077_alpha_dummy_314 x) := by
  simpa only [nb077_alpha_dummy_313, nb077_alpha_dummy_314] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_095 (F : Class) (I : Class) : (nb077_alpha_dummy_075 F I) ∉ (((Class.cv (nb077_alpha_dummy_068 F I))).fv) := by
  simpa only [nb077_alpha_dummy_075] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_068 F I))).fv) 0

theorem nb077_fresh_096 (F : Class) (I : Class) : (nb077_alpha_dummy_076 F I) ∉ (((Class.cv (nb077_alpha_dummy_068 F I))).fv) := by
  simpa only [nb077_alpha_dummy_076] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_068 F I))).fv) 1

theorem nb077_distinct_097 (F : Class) (I : Class) : (nb077_alpha_dummy_075 F I) ≠ (nb077_alpha_dummy_076 F I) := by
  simpa only [nb077_alpha_dummy_075, nb077_alpha_dummy_076] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_068 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_098 (x : Var) : (nb077_alpha_dummy_077 x) ∉ (((Class.cv (nb077_alpha_dummy_070 x))).fv) := by
  simpa only [nb077_alpha_dummy_077] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_070 x))).fv) 0

theorem nb077_fresh_099 (x : Var) : (nb077_alpha_dummy_078 x) ∉ (((Class.cv (nb077_alpha_dummy_070 x))).fv) := by
  simpa only [nb077_alpha_dummy_078] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_070 x))).fv) 1

theorem nb077_distinct_100 (x : Var) : (nb077_alpha_dummy_077 x) ≠ (nb077_alpha_dummy_078 x) := by
  simpa only [nb077_alpha_dummy_077, nb077_alpha_dummy_078] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_070 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_101 (F : Class) (I : Class) : (nb077_alpha_dummy_081 F I) ∉ (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_081] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_102 (F : Class) (I : Class) : (nb077_alpha_dummy_082 F I) ∉ (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_082] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_103 (F : Class) (I : Class) : (nb077_alpha_dummy_083 F I) ∉ (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_083] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_104 (F : Class) (I : Class) : (nb077_alpha_dummy_081 F I) ≠ (nb077_alpha_dummy_082 F I) := by
  simpa only [nb077_alpha_dummy_081, nb077_alpha_dummy_082] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_105 (F : Class) (I : Class) : (nb077_alpha_dummy_081 F I) ≠ (nb077_alpha_dummy_083 F I) := by
  simpa only [nb077_alpha_dummy_081, nb077_alpha_dummy_083] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_106 (F : Class) (I : Class) : (nb077_alpha_dummy_082 F I) ≠ (nb077_alpha_dummy_083 F I) := by
  simpa only [nb077_alpha_dummy_082, nb077_alpha_dummy_083] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_075 F I))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_107 (x : Var) : (nb077_alpha_dummy_084 x) ∉ (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_084] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_108 (x : Var) : (nb077_alpha_dummy_085 x) ∉ (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_085] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_109 (x : Var) : (nb077_alpha_dummy_086 x) ∉ (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_086] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_110 (x : Var) : (nb077_alpha_dummy_084 x) ≠ (nb077_alpha_dummy_085 x) := by
  simpa only [nb077_alpha_dummy_084, nb077_alpha_dummy_085] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_111 (x : Var) : (nb077_alpha_dummy_084 x) ≠ (nb077_alpha_dummy_086 x) := by
  simpa only [nb077_alpha_dummy_084, nb077_alpha_dummy_086] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_112 (x : Var) : (nb077_alpha_dummy_085 x) ≠ (nb077_alpha_dummy_086 x) := by
  simpa only [nb077_alpha_dummy_085, nb077_alpha_dummy_086] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_077 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_113 (F : Class) (I : Class) : (nb077_alpha_dummy_093 F I) ∉ (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_082 F I))).fv) := by
  simpa only [nb077_alpha_dummy_093] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_082 F I))).fv) 0

theorem nb077_fresh_114 (F : Class) (I : Class) : (nb077_alpha_dummy_089 F I) ∉ (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_083 F I))).fv) := by
  simpa only [nb077_alpha_dummy_089] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_082 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_083 F I))).fv) 0

theorem nb077_fresh_115 (F : Class) (I : Class) : (nb077_alpha_dummy_095 F I) ∉ (((Class.cv (nb077_alpha_dummy_083 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_083 F I))).fv) := by
  simpa only [nb077_alpha_dummy_095] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_083 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_083 F I))).fv) 0

theorem nb077_fresh_116 (x : Var) : (nb077_alpha_dummy_094 x) ∉ (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_085 x))).fv) := by
  simpa only [nb077_alpha_dummy_094] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_085 x))).fv) 0

theorem nb077_fresh_117 (x : Var) : (nb077_alpha_dummy_090 x) ∉ (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) := by
  simpa only [nb077_alpha_dummy_090] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_085 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) 0

theorem nb077_fresh_118 (x : Var) : (nb077_alpha_dummy_096 x) ∉ (((Class.cv (nb077_alpha_dummy_086 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) := by
  simpa only [nb077_alpha_dummy_096] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_086 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_086 x))).fv) 0

theorem nb077_fresh_119 (F : Class) (I : Class) : (nb077_alpha_dummy_111 F I) ∉ (((Class.cv (nb077_alpha_dummy_104 F I))).fv) := by
  simpa only [nb077_alpha_dummy_111] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_104 F I))).fv) 0

theorem nb077_fresh_120 (F : Class) (I : Class) : (nb077_alpha_dummy_112 F I) ∉ (((Class.cv (nb077_alpha_dummy_104 F I))).fv) := by
  simpa only [nb077_alpha_dummy_112] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_104 F I))).fv) 1

theorem nb077_distinct_121 (F : Class) (I : Class) : (nb077_alpha_dummy_111 F I) ≠ (nb077_alpha_dummy_112 F I) := by
  simpa only [nb077_alpha_dummy_111, nb077_alpha_dummy_112] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_104 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_122 (x : Var) : (nb077_alpha_dummy_113 x) ∉ (((Class.cv (nb077_alpha_dummy_106 x))).fv) := by
  simpa only [nb077_alpha_dummy_113] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_106 x))).fv) 0

theorem nb077_fresh_123 (x : Var) : (nb077_alpha_dummy_114 x) ∉ (((Class.cv (nb077_alpha_dummy_106 x))).fv) := by
  simpa only [nb077_alpha_dummy_114] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_106 x))).fv) 1

theorem nb077_distinct_124 (x : Var) : (nb077_alpha_dummy_113 x) ≠ (nb077_alpha_dummy_114 x) := by
  simpa only [nb077_alpha_dummy_113, nb077_alpha_dummy_114] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_106 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_125 (F : Class) (I : Class) : (nb077_alpha_dummy_117 F I) ∉ (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_117] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_126 (F : Class) (I : Class) : (nb077_alpha_dummy_118 F I) ∉ (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_118] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_127 (F : Class) (I : Class) : (nb077_alpha_dummy_119 F I) ∉ (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_119] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_128 (F : Class) (I : Class) : (nb077_alpha_dummy_117 F I) ≠ (nb077_alpha_dummy_118 F I) := by
  simpa only [nb077_alpha_dummy_117, nb077_alpha_dummy_118] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_129 (F : Class) (I : Class) : (nb077_alpha_dummy_117 F I) ≠ (nb077_alpha_dummy_119 F I) := by
  simpa only [nb077_alpha_dummy_117, nb077_alpha_dummy_119] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_130 (F : Class) (I : Class) : (nb077_alpha_dummy_118 F I) ≠ (nb077_alpha_dummy_119 F I) := by
  simpa only [nb077_alpha_dummy_118, nb077_alpha_dummy_119] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_131 (x : Var) : (nb077_alpha_dummy_120 x) ∉ (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_120] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_132 (x : Var) : (nb077_alpha_dummy_121 x) ∉ (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_121] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_133 (x : Var) : (nb077_alpha_dummy_122 x) ∉ (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_122] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_134 (x : Var) : (nb077_alpha_dummy_120 x) ≠ (nb077_alpha_dummy_121 x) := by
  simpa only [nb077_alpha_dummy_120, nb077_alpha_dummy_121] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_135 (x : Var) : (nb077_alpha_dummy_120 x) ≠ (nb077_alpha_dummy_122 x) := by
  simpa only [nb077_alpha_dummy_120, nb077_alpha_dummy_122] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_136 (x : Var) : (nb077_alpha_dummy_121 x) ≠ (nb077_alpha_dummy_122 x) := by
  simpa only [nb077_alpha_dummy_121, nb077_alpha_dummy_122] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_137 (F : Class) (I : Class) : (nb077_alpha_dummy_129 F I) ∉ (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_118 F I))).fv) := by
  simpa only [nb077_alpha_dummy_129] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_118 F I))).fv) 0

theorem nb077_fresh_138 (F : Class) (I : Class) : (nb077_alpha_dummy_125 F I) ∉ (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_119 F I))).fv) := by
  simpa only [nb077_alpha_dummy_125] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_118 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_119 F I))).fv) 0

theorem nb077_fresh_139 (F : Class) (I : Class) : (nb077_alpha_dummy_131 F I) ∉ (((Class.cv (nb077_alpha_dummy_119 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_119 F I))).fv) := by
  simpa only [nb077_alpha_dummy_131] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_119 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_119 F I))).fv) 0

theorem nb077_fresh_140 (x : Var) : (nb077_alpha_dummy_130 x) ∉ (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_121 x))).fv) := by
  simpa only [nb077_alpha_dummy_130] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_121 x))).fv) 0

theorem nb077_fresh_141 (x : Var) : (nb077_alpha_dummy_126 x) ∉ (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) := by
  simpa only [nb077_alpha_dummy_126] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_121 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) 0

theorem nb077_fresh_142 (x : Var) : (nb077_alpha_dummy_132 x) ∉ (((Class.cv (nb077_alpha_dummy_122 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) := by
  simpa only [nb077_alpha_dummy_132] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_122 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_122 x))).fv) 0

theorem nb077_fresh_143 (F : Class) (I : Class) : (nb077_alpha_dummy_147 F I) ∉ (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) := by
  simpa only [nb077_alpha_dummy_147] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 0

theorem nb077_fresh_144 (F : Class) (I : Class) : (nb077_alpha_dummy_148 F I) ∉ (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) := by
  simpa only [nb077_alpha_dummy_148] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 1

theorem nb077_distinct_145 (F : Class) (I : Class) : (nb077_alpha_dummy_147 F I) ≠ (nb077_alpha_dummy_148 F I) := by
  simpa only [nb077_alpha_dummy_147, nb077_alpha_dummy_148] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_146 (F : Class) (I : Class) : (nb077_alpha_dummy_183 F I) ∉ (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_141 F I))).fv) := by
  simpa only [nb077_alpha_dummy_183] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_141 F I))).fv) 0

theorem nb077_fresh_147 (F : Class) (I : Class) : (nb077_alpha_dummy_184 F I) ∉ (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_141 F I))).fv) := by
  simpa only [nb077_alpha_dummy_184] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_141 F I))).fv) 1

theorem nb077_distinct_148 (F : Class) (I : Class) : (nb077_alpha_dummy_183 F I) ≠ (nb077_alpha_dummy_184 F I) := by
  simpa only [nb077_alpha_dummy_183, nb077_alpha_dummy_184] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_141 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_149 (F : Class) (I : Class) : (nb077_alpha_dummy_219 F I) ∉ (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) := by
  simpa only [nb077_alpha_dummy_219] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 0

theorem nb077_fresh_150 (F : Class) (I : Class) : (nb077_alpha_dummy_220 F I) ∉ (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) := by
  simpa only [nb077_alpha_dummy_220] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) 1

theorem nb077_distinct_151 (F : Class) (I : Class) : (nb077_alpha_dummy_219 F I) ≠ (nb077_alpha_dummy_220 F I) := by
  simpa only [nb077_alpha_dummy_219, nb077_alpha_dummy_220] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_141 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_152 (x : Var) : (nb077_alpha_dummy_149 x) ∉ (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) := by
  simpa only [nb077_alpha_dummy_149] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) 0

theorem nb077_fresh_153 (x : Var) : (nb077_alpha_dummy_150 x) ∉ (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) := by
  simpa only [nb077_alpha_dummy_150] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) 1

theorem nb077_distinct_154 (x : Var) : (nb077_alpha_dummy_149 x) ≠ (nb077_alpha_dummy_150 x) := by
  simpa only [nb077_alpha_dummy_149, nb077_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_155 (x : Var) : (nb077_alpha_dummy_185 x) ∉ (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) := by
  simpa only [nb077_alpha_dummy_185] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) 0

theorem nb077_fresh_156 (x : Var) : (nb077_alpha_dummy_186 x) ∉ (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) := by
  simpa only [nb077_alpha_dummy_186] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) 1

theorem nb077_distinct_157 (x : Var) : (nb077_alpha_dummy_185 x) ≠ (nb077_alpha_dummy_186 x) := by
  simpa only [nb077_alpha_dummy_185, nb077_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_144 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_158 (x : Var) : (nb077_alpha_dummy_221 x) ∉ (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) := by
  simpa only [nb077_alpha_dummy_221] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) 0

theorem nb077_fresh_159 (x : Var) : (nb077_alpha_dummy_222 x) ∉ (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) := by
  simpa only [nb077_alpha_dummy_222] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) 1

theorem nb077_distinct_160 (x : Var) : (nb077_alpha_dummy_221 x) ≠ (nb077_alpha_dummy_222 x) := by
  simpa only [nb077_alpha_dummy_221, nb077_alpha_dummy_222] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_144 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_143 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_161 (F : Class) (I : Class) : (nb077_alpha_dummy_155 F I) ∉ (((Class.cv (nb077_alpha_dummy_148 F I))).fv) := by
  simpa only [nb077_alpha_dummy_155] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_148 F I))).fv) 0

theorem nb077_fresh_162 (F : Class) (I : Class) : (nb077_alpha_dummy_156 F I) ∉ (((Class.cv (nb077_alpha_dummy_148 F I))).fv) := by
  simpa only [nb077_alpha_dummy_156] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_148 F I))).fv) 1

theorem nb077_distinct_163 (F : Class) (I : Class) : (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_156 F I) := by
  simpa only [nb077_alpha_dummy_155, nb077_alpha_dummy_156] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_148 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_164 (x : Var) : (nb077_alpha_dummy_157 x) ∉ (((Class.cv (nb077_alpha_dummy_150 x))).fv) := by
  simpa only [nb077_alpha_dummy_157] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_150 x))).fv) 0

theorem nb077_fresh_165 (x : Var) : (nb077_alpha_dummy_158 x) ∉ (((Class.cv (nb077_alpha_dummy_150 x))).fv) := by
  simpa only [nb077_alpha_dummy_158] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_150 x))).fv) 1

theorem nb077_distinct_166 (x : Var) : (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_158 x) := by
  simpa only [nb077_alpha_dummy_157, nb077_alpha_dummy_158] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_150 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_167 (F : Class) (I : Class) : (nb077_alpha_dummy_161 F I) ∉ (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_161] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_168 (F : Class) (I : Class) : (nb077_alpha_dummy_162 F I) ∉ (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_162] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_169 (F : Class) (I : Class) : (nb077_alpha_dummy_163 F I) ∉ (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_163] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_170 (F : Class) (I : Class) : (nb077_alpha_dummy_161 F I) ≠ (nb077_alpha_dummy_162 F I) := by
  simpa only [nb077_alpha_dummy_161, nb077_alpha_dummy_162] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_171 (F : Class) (I : Class) : (nb077_alpha_dummy_161 F I) ≠ (nb077_alpha_dummy_163 F I) := by
  simpa only [nb077_alpha_dummy_161, nb077_alpha_dummy_163] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_172 (F : Class) (I : Class) : (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_163 F I) := by
  simpa only [nb077_alpha_dummy_162, nb077_alpha_dummy_163] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_173 (x : Var) : (nb077_alpha_dummy_164 x) ∉ (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_164] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_174 (x : Var) : (nb077_alpha_dummy_165 x) ∉ (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_165] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_175 (x : Var) : (nb077_alpha_dummy_166 x) ∉ (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_166] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_176 (x : Var) : (nb077_alpha_dummy_164 x) ≠ (nb077_alpha_dummy_165 x) := by
  simpa only [nb077_alpha_dummy_164, nb077_alpha_dummy_165] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_177 (x : Var) : (nb077_alpha_dummy_164 x) ≠ (nb077_alpha_dummy_166 x) := by
  simpa only [nb077_alpha_dummy_164, nb077_alpha_dummy_166] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_178 (x : Var) : (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_166 x) := by
  simpa only [nb077_alpha_dummy_165, nb077_alpha_dummy_166] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_179 (F : Class) (I : Class) : (nb077_alpha_dummy_173 F I) ∉ (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_162 F I))).fv) := by
  simpa only [nb077_alpha_dummy_173] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_162 F I))).fv) 0

theorem nb077_fresh_180 (F : Class) (I : Class) : (nb077_alpha_dummy_169 F I) ∉ (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_163 F I))).fv) := by
  simpa only [nb077_alpha_dummy_169] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_162 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_163 F I))).fv) 0

theorem nb077_fresh_181 (F : Class) (I : Class) : (nb077_alpha_dummy_175 F I) ∉ (((Class.cv (nb077_alpha_dummy_163 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_163 F I))).fv) := by
  simpa only [nb077_alpha_dummy_175] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_163 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_163 F I))).fv) 0

theorem nb077_fresh_182 (x : Var) : (nb077_alpha_dummy_174 x) ∉ (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_165 x))).fv) := by
  simpa only [nb077_alpha_dummy_174] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_165 x))).fv) 0

theorem nb077_fresh_183 (x : Var) : (nb077_alpha_dummy_170 x) ∉ (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) := by
  simpa only [nb077_alpha_dummy_170] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_165 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) 0

theorem nb077_fresh_184 (x : Var) : (nb077_alpha_dummy_176 x) ∉ (((Class.cv (nb077_alpha_dummy_166 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) := by
  simpa only [nb077_alpha_dummy_176] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_166 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_166 x))).fv) 0

theorem nb077_fresh_185 (F : Class) (I : Class) : (nb077_alpha_dummy_191 F I) ∉ (((Class.cv (nb077_alpha_dummy_184 F I))).fv) := by
  simpa only [nb077_alpha_dummy_191] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_184 F I))).fv) 0

theorem nb077_fresh_186 (F : Class) (I : Class) : (nb077_alpha_dummy_192 F I) ∉ (((Class.cv (nb077_alpha_dummy_184 F I))).fv) := by
  simpa only [nb077_alpha_dummy_192] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_184 F I))).fv) 1

theorem nb077_distinct_187 (F : Class) (I : Class) : (nb077_alpha_dummy_191 F I) ≠ (nb077_alpha_dummy_192 F I) := by
  simpa only [nb077_alpha_dummy_191, nb077_alpha_dummy_192] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_184 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_188 (x : Var) : (nb077_alpha_dummy_193 x) ∉ (((Class.cv (nb077_alpha_dummy_186 x))).fv) := by
  simpa only [nb077_alpha_dummy_193] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_186 x))).fv) 0

theorem nb077_fresh_189 (x : Var) : (nb077_alpha_dummy_194 x) ∉ (((Class.cv (nb077_alpha_dummy_186 x))).fv) := by
  simpa only [nb077_alpha_dummy_194] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_186 x))).fv) 1

theorem nb077_distinct_190 (x : Var) : (nb077_alpha_dummy_193 x) ≠ (nb077_alpha_dummy_194 x) := by
  simpa only [nb077_alpha_dummy_193, nb077_alpha_dummy_194] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_186 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_191 (F : Class) (I : Class) : (nb077_alpha_dummy_197 F I) ∉ (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_197] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_192 (F : Class) (I : Class) : (nb077_alpha_dummy_198 F I) ∉ (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_198] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_193 (F : Class) (I : Class) : (nb077_alpha_dummy_199 F I) ∉ (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_199] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_194 (F : Class) (I : Class) : (nb077_alpha_dummy_197 F I) ≠ (nb077_alpha_dummy_198 F I) := by
  simpa only [nb077_alpha_dummy_197, nb077_alpha_dummy_198] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_195 (F : Class) (I : Class) : (nb077_alpha_dummy_197 F I) ≠ (nb077_alpha_dummy_199 F I) := by
  simpa only [nb077_alpha_dummy_197, nb077_alpha_dummy_199] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_196 (F : Class) (I : Class) : (nb077_alpha_dummy_198 F I) ≠ (nb077_alpha_dummy_199 F I) := by
  simpa only [nb077_alpha_dummy_198, nb077_alpha_dummy_199] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_191 F I))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_197 (x : Var) : (nb077_alpha_dummy_200 x) ∉ (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_200] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_198 (x : Var) : (nb077_alpha_dummy_201 x) ∉ (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_201] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_199 (x : Var) : (nb077_alpha_dummy_202 x) ∉ (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_202] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_200 (x : Var) : (nb077_alpha_dummy_200 x) ≠ (nb077_alpha_dummy_201 x) := by
  simpa only [nb077_alpha_dummy_200, nb077_alpha_dummy_201] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_201 (x : Var) : (nb077_alpha_dummy_200 x) ≠ (nb077_alpha_dummy_202 x) := by
  simpa only [nb077_alpha_dummy_200, nb077_alpha_dummy_202] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_202 (x : Var) : (nb077_alpha_dummy_201 x) ≠ (nb077_alpha_dummy_202 x) := by
  simpa only [nb077_alpha_dummy_201, nb077_alpha_dummy_202] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_193 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_203 (F : Class) (I : Class) : (nb077_alpha_dummy_209 F I) ∉ (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_198 F I))).fv) := by
  simpa only [nb077_alpha_dummy_209] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_198 F I))).fv) 0

theorem nb077_fresh_204 (F : Class) (I : Class) : (nb077_alpha_dummy_205 F I) ∉ (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_199 F I))).fv) := by
  simpa only [nb077_alpha_dummy_205] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_198 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_199 F I))).fv) 0

theorem nb077_fresh_205 (F : Class) (I : Class) : (nb077_alpha_dummy_211 F I) ∉ (((Class.cv (nb077_alpha_dummy_199 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_199 F I))).fv) := by
  simpa only [nb077_alpha_dummy_211] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_199 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_199 F I))).fv) 0

theorem nb077_fresh_206 (x : Var) : (nb077_alpha_dummy_210 x) ∉ (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_201 x))).fv) := by
  simpa only [nb077_alpha_dummy_210] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_201 x))).fv) 0

theorem nb077_fresh_207 (x : Var) : (nb077_alpha_dummy_206 x) ∉ (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) := by
  simpa only [nb077_alpha_dummy_206] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_201 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) 0

theorem nb077_fresh_208 (x : Var) : (nb077_alpha_dummy_212 x) ∉ (((Class.cv (nb077_alpha_dummy_202 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) := by
  simpa only [nb077_alpha_dummy_212] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_202 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_202 x))).fv) 0

theorem nb077_fresh_209 (F : Class) (I : Class) : (nb077_alpha_dummy_227 F I) ∉ (((Class.cv (nb077_alpha_dummy_220 F I))).fv) := by
  simpa only [nb077_alpha_dummy_227] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_220 F I))).fv) 0

theorem nb077_fresh_210 (F : Class) (I : Class) : (nb077_alpha_dummy_228 F I) ∉ (((Class.cv (nb077_alpha_dummy_220 F I))).fv) := by
  simpa only [nb077_alpha_dummy_228] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_220 F I))).fv) 1

theorem nb077_distinct_211 (F : Class) (I : Class) : (nb077_alpha_dummy_227 F I) ≠ (nb077_alpha_dummy_228 F I) := by
  simpa only [nb077_alpha_dummy_227, nb077_alpha_dummy_228] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_220 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_212 (x : Var) : (nb077_alpha_dummy_229 x) ∉ (((Class.cv (nb077_alpha_dummy_222 x))).fv) := by
  simpa only [nb077_alpha_dummy_229] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_222 x))).fv) 0

theorem nb077_fresh_213 (x : Var) : (nb077_alpha_dummy_230 x) ∉ (((Class.cv (nb077_alpha_dummy_222 x))).fv) := by
  simpa only [nb077_alpha_dummy_230] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_222 x))).fv) 1

theorem nb077_distinct_214 (x : Var) : (nb077_alpha_dummy_229 x) ≠ (nb077_alpha_dummy_230 x) := by
  simpa only [nb077_alpha_dummy_229, nb077_alpha_dummy_230] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_222 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_215 (F : Class) (I : Class) : (nb077_alpha_dummy_233 F I) ∉ (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_233] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_216 (F : Class) (I : Class) : (nb077_alpha_dummy_234 F I) ∉ (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_234] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_217 (F : Class) (I : Class) : (nb077_alpha_dummy_235 F I) ∉ (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_235] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_218 (F : Class) (I : Class) : (nb077_alpha_dummy_233 F I) ≠ (nb077_alpha_dummy_234 F I) := by
  simpa only [nb077_alpha_dummy_233, nb077_alpha_dummy_234] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
