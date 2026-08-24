import NAR4C056C001Part002

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

theorem nb056_fresh_101 (f : Var) : (nb056_alpha_dummy_093 f) ∉ (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) := by
  simpa only [nb056_alpha_dummy_093] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) 0

theorem nb056_fresh_102 (f : Var) : (nb056_alpha_dummy_094 f) ∉ (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) := by
  simpa only [nb056_alpha_dummy_094] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) 1

theorem nb056_distinct_103 (f : Var) : (nb056_alpha_dummy_093 f) ≠ (nb056_alpha_dummy_094 f) := by
  simpa only [nb056_alpha_dummy_093, nb056_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_104 (f : Var) : (nb056_alpha_dummy_129 f) ∉ (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) := by
  simpa only [nb056_alpha_dummy_129] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) 0

theorem nb056_fresh_105 (f : Var) : (nb056_alpha_dummy_130 f) ∉ (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) := by
  simpa only [nb056_alpha_dummy_130] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) 1

theorem nb056_distinct_106 (f : Var) : (nb056_alpha_dummy_129 f) ≠ (nb056_alpha_dummy_130 f) := by
  simpa only [nb056_alpha_dummy_129, nb056_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_107 : (nb056_alpha_dummy_099) ∉ (((Class.cv (nb056_alpha_dummy_092))).fv) := by
  simpa only [nb056_alpha_dummy_099] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_092))).fv) 0

theorem nb056_fresh_108 : (nb056_alpha_dummy_100) ∉ (((Class.cv (nb056_alpha_dummy_092))).fv) := by
  simpa only [nb056_alpha_dummy_100] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_092))).fv) 1

theorem nb056_distinct_109 : (nb056_alpha_dummy_099) ≠ (nb056_alpha_dummy_100) := by
  simpa only [nb056_alpha_dummy_099, nb056_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_092))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_110 (f : Var) : (nb056_alpha_dummy_101 f) ∉ (((Class.cv (nb056_alpha_dummy_094 f))).fv) := by
  simpa only [nb056_alpha_dummy_101] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_094 f))).fv) 0

theorem nb056_fresh_111 (f : Var) : (nb056_alpha_dummy_102 f) ∉ (((Class.cv (nb056_alpha_dummy_094 f))).fv) := by
  simpa only [nb056_alpha_dummy_102] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_094 f))).fv) 1

theorem nb056_distinct_112 (f : Var) : (nb056_alpha_dummy_101 f) ≠ (nb056_alpha_dummy_102 f) := by
  simpa only [nb056_alpha_dummy_101, nb056_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_094 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_113 : (nb056_alpha_dummy_105) ∉ (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_105] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_114 : (nb056_alpha_dummy_106) ∉ (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_106] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_115 : (nb056_alpha_dummy_107) ∉ (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_107] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_116 : (nb056_alpha_dummy_105) ≠ (nb056_alpha_dummy_106) := by
  simpa only [nb056_alpha_dummy_105, nb056_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_117 : (nb056_alpha_dummy_105) ≠ (nb056_alpha_dummy_107) := by
  simpa only [nb056_alpha_dummy_105, nb056_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_118 : (nb056_alpha_dummy_106) ≠ (nb056_alpha_dummy_107) := by
  simpa only [nb056_alpha_dummy_106, nb056_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_119 (f : Var) : (nb056_alpha_dummy_108 f) ∉ (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_108] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_120 (f : Var) : (nb056_alpha_dummy_109 f) ∉ (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_109] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_121 (f : Var) : (nb056_alpha_dummy_110 f) ∉ (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_110] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_122 (f : Var) : (nb056_alpha_dummy_108 f) ≠ (nb056_alpha_dummy_109 f) := by
  simpa only [nb056_alpha_dummy_108, nb056_alpha_dummy_109] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_123 (f : Var) : (nb056_alpha_dummy_108 f) ≠ (nb056_alpha_dummy_110 f) := by
  simpa only [nb056_alpha_dummy_108, nb056_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_124 (f : Var) : (nb056_alpha_dummy_109 f) ≠ (nb056_alpha_dummy_110 f) := by
  simpa only [nb056_alpha_dummy_109, nb056_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_125 : (nb056_alpha_dummy_117) ∉ (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_106))).fv) := by
  simpa only [nb056_alpha_dummy_117] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_106))).fv) 0

theorem nb056_fresh_126 : (nb056_alpha_dummy_113) ∉ (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) := by
  simpa only [nb056_alpha_dummy_113] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) 0

theorem nb056_fresh_127 : (nb056_alpha_dummy_119) ∉ (((Class.cv (nb056_alpha_dummy_107))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) := by
  simpa only [nb056_alpha_dummy_119] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_107))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) 0

theorem nb056_fresh_128 (f : Var) : (nb056_alpha_dummy_118 f) ∉ (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_109 f))).fv) := by
  simpa only [nb056_alpha_dummy_118] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_109 f))).fv) 0

theorem nb056_fresh_129 (f : Var) : (nb056_alpha_dummy_114 f) ∉ (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) := by
  simpa only [nb056_alpha_dummy_114] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) 0

theorem nb056_fresh_130 (f : Var) : (nb056_alpha_dummy_120 f) ∉ (((Class.cv (nb056_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) := by
  simpa only [nb056_alpha_dummy_120] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) 0

theorem nb056_fresh_131 : (nb056_alpha_dummy_135) ∉ (((Class.cv (nb056_alpha_dummy_128))).fv) := by
  simpa only [nb056_alpha_dummy_135] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_128))).fv) 0

theorem nb056_fresh_132 : (nb056_alpha_dummy_136) ∉ (((Class.cv (nb056_alpha_dummy_128))).fv) := by
  simpa only [nb056_alpha_dummy_136] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_128))).fv) 1

theorem nb056_distinct_133 : (nb056_alpha_dummy_135) ≠ (nb056_alpha_dummy_136) := by
  simpa only [nb056_alpha_dummy_135, nb056_alpha_dummy_136] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_128))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_134 (f : Var) : (nb056_alpha_dummy_137 f) ∉ (((Class.cv (nb056_alpha_dummy_130 f))).fv) := by
  simpa only [nb056_alpha_dummy_137] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_130 f))).fv) 0

theorem nb056_fresh_135 (f : Var) : (nb056_alpha_dummy_138 f) ∉ (((Class.cv (nb056_alpha_dummy_130 f))).fv) := by
  simpa only [nb056_alpha_dummy_138] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_130 f))).fv) 1

theorem nb056_distinct_136 (f : Var) : (nb056_alpha_dummy_137 f) ≠ (nb056_alpha_dummy_138 f) := by
  simpa only [nb056_alpha_dummy_137, nb056_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_130 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_137 : (nb056_alpha_dummy_141) ∉ (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_141] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_138 : (nb056_alpha_dummy_142) ∉ (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_142] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_139 : (nb056_alpha_dummy_143) ∉ (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_143] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_140 : (nb056_alpha_dummy_141) ≠ (nb056_alpha_dummy_142) := by
  simpa only [nb056_alpha_dummy_141, nb056_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_141 : (nb056_alpha_dummy_141) ≠ (nb056_alpha_dummy_143) := by
  simpa only [nb056_alpha_dummy_141, nb056_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_142 : (nb056_alpha_dummy_142) ≠ (nb056_alpha_dummy_143) := by
  simpa only [nb056_alpha_dummy_142, nb056_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_143 (f : Var) : (nb056_alpha_dummy_144 f) ∉ (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_144] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_144 (f : Var) : (nb056_alpha_dummy_145 f) ∉ (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_145] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_145 (f : Var) : (nb056_alpha_dummy_146 f) ∉ (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_146] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_146 (f : Var) : (nb056_alpha_dummy_144 f) ≠ (nb056_alpha_dummy_145 f) := by
  simpa only [nb056_alpha_dummy_144, nb056_alpha_dummy_145] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_147 (f : Var) : (nb056_alpha_dummy_144 f) ≠ (nb056_alpha_dummy_146 f) := by
  simpa only [nb056_alpha_dummy_144, nb056_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_148 (f : Var) : (nb056_alpha_dummy_145 f) ≠ (nb056_alpha_dummy_146 f) := by
  simpa only [nb056_alpha_dummy_145, nb056_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_149 : (nb056_alpha_dummy_153) ∉ (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_142))).fv) := by
  simpa only [nb056_alpha_dummy_153] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_142))).fv) 0

theorem nb056_fresh_150 : (nb056_alpha_dummy_149) ∉ (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) := by
  simpa only [nb056_alpha_dummy_149] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) 0

theorem nb056_fresh_151 : (nb056_alpha_dummy_155) ∉ (((Class.cv (nb056_alpha_dummy_143))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) := by
  simpa only [nb056_alpha_dummy_155] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_143))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) 0

theorem nb056_fresh_152 (f : Var) : (nb056_alpha_dummy_154 f) ∉ (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_145 f))).fv) := by
  simpa only [nb056_alpha_dummy_154] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_145 f))).fv) 0

theorem nb056_fresh_153 (f : Var) : (nb056_alpha_dummy_150 f) ∉ (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) := by
  simpa only [nb056_alpha_dummy_150] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) 0

theorem nb056_fresh_154 (f : Var) : (nb056_alpha_dummy_156 f) ∉ (((Class.cv (nb056_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) := by
  simpa only [nb056_alpha_dummy_156] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) 0

theorem nb056_fresh_155 : (nb056_alpha_dummy_171) ∉ (((Class.cv (nb056_alpha_dummy_164))).fv) := by
  simpa only [nb056_alpha_dummy_171] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_164))).fv) 0

theorem nb056_fresh_156 : (nb056_alpha_dummy_172) ∉ (((Class.cv (nb056_alpha_dummy_164))).fv) := by
  simpa only [nb056_alpha_dummy_172] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_164))).fv) 1

theorem nb056_distinct_157 : (nb056_alpha_dummy_171) ≠ (nb056_alpha_dummy_172) := by
  simpa only [nb056_alpha_dummy_171, nb056_alpha_dummy_172] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_164))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_158 (f : Var) : (nb056_alpha_dummy_173 f) ∉ (((Class.cv (nb056_alpha_dummy_166 f))).fv) := by
  simpa only [nb056_alpha_dummy_173] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_166 f))).fv) 0

theorem nb056_fresh_159 (f : Var) : (nb056_alpha_dummy_174 f) ∉ (((Class.cv (nb056_alpha_dummy_166 f))).fv) := by
  simpa only [nb056_alpha_dummy_174] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_166 f))).fv) 1

theorem nb056_distinct_160 (f : Var) : (nb056_alpha_dummy_173 f) ≠ (nb056_alpha_dummy_174 f) := by
  simpa only [nb056_alpha_dummy_173, nb056_alpha_dummy_174] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_166 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_161 : (nb056_alpha_dummy_177) ∉ (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_177] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_162 : (nb056_alpha_dummy_178) ∉ (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_178] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_163 : (nb056_alpha_dummy_179) ∉ (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_179] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_164 : (nb056_alpha_dummy_177) ≠ (nb056_alpha_dummy_178) := by
  simpa only [nb056_alpha_dummy_177, nb056_alpha_dummy_178] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_165 : (nb056_alpha_dummy_177) ≠ (nb056_alpha_dummy_179) := by
  simpa only [nb056_alpha_dummy_177, nb056_alpha_dummy_179] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_166 : (nb056_alpha_dummy_178) ≠ (nb056_alpha_dummy_179) := by
  simpa only [nb056_alpha_dummy_178, nb056_alpha_dummy_179] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_167 (f : Var) : (nb056_alpha_dummy_180 f) ∉ (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_180] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_168 (f : Var) : (nb056_alpha_dummy_181 f) ∉ (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_181] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_169 (f : Var) : (nb056_alpha_dummy_182 f) ∉ (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb056_alpha_dummy_182] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_170 (f : Var) : (nb056_alpha_dummy_180 f) ≠ (nb056_alpha_dummy_181 f) := by
  simpa only [nb056_alpha_dummy_180, nb056_alpha_dummy_181] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_171 (f : Var) : (nb056_alpha_dummy_180 f) ≠ (nb056_alpha_dummy_182 f) := by
  simpa only [nb056_alpha_dummy_180, nb056_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_172 (f : Var) : (nb056_alpha_dummy_181 f) ≠ (nb056_alpha_dummy_182 f) := by
  simpa only [nb056_alpha_dummy_181, nb056_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_173 : (nb056_alpha_dummy_189) ∉ (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_178))).fv) := by
  simpa only [nb056_alpha_dummy_189] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_178))).fv) 0

theorem nb056_fresh_174 : (nb056_alpha_dummy_185) ∉ (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) := by
  simpa only [nb056_alpha_dummy_185] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) 0

theorem nb056_fresh_175 : (nb056_alpha_dummy_191) ∉ (((Class.cv (nb056_alpha_dummy_179))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) := by
  simpa only [nb056_alpha_dummy_191] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_179))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) 0

theorem nb056_fresh_176 (f : Var) : (nb056_alpha_dummy_190 f) ∉ (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_181 f))).fv) := by
  simpa only [nb056_alpha_dummy_190] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_181 f))).fv) 0

theorem nb056_fresh_177 (f : Var) : (nb056_alpha_dummy_186 f) ∉ (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) := by
  simpa only [nb056_alpha_dummy_186] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) 0

theorem nb056_fresh_178 (f : Var) : (nb056_alpha_dummy_192 f) ∉ (((Class.cv (nb056_alpha_dummy_182 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) := by
  simpa only [nb056_alpha_dummy_192] using freshVar_not_mem (((Class.cv (nb056_alpha_dummy_182 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) 0

theorem nb056_fresh_179 (f : Var) : (nb056_alpha_dummy_087 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb056_alpha_dummy_087] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb056_fresh_180 (f : Var) : (nb056_alpha_dummy_088 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb056_alpha_dummy_088] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb056_distinct_181 (f : Var) : (nb056_alpha_dummy_087 f) ≠ (nb056_alpha_dummy_088 f) := by
  simpa only [nb056_alpha_dummy_087, nb056_alpha_dummy_088] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_182 (f : Var) : (nb056_alpha_dummy_008 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb056_alpha_dummy_008] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb056_fresh_183 (f : Var) : (nb056_alpha_dummy_009 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb056_alpha_dummy_009] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb056_fresh_184 (f : Var) : (nb056_alpha_dummy_010 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb056_alpha_dummy_010] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb056_distinct_185 (f : Var) : (nb056_alpha_dummy_008 f) ≠ (nb056_alpha_dummy_009 f) := by
  simpa only [nb056_alpha_dummy_008, nb056_alpha_dummy_009] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_186 (f : Var) : (nb056_alpha_dummy_008 f) ≠ (nb056_alpha_dummy_010 f) := by
  simpa only [nb056_alpha_dummy_008, nb056_alpha_dummy_010] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_187 (f : Var) : (nb056_alpha_dummy_009 f) ≠ (nb056_alpha_dummy_010 f) := by
  simpa only [nb056_alpha_dummy_009, nb056_alpha_dummy_010] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_188 : (nb056_alpha_dummy_025) ∉ (((Wff.classMem (Class.cv (nb056_alpha_dummy_021)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_021)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_021))).fv) := by
  simpa only [nb056_alpha_dummy_025] using freshVar_not_mem (((Wff.classMem (Class.cv (nb056_alpha_dummy_021)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_021)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_021))).fv) 0

theorem nb056_fresh_189 (f : Var) : (nb056_alpha_dummy_026 f) ∉ (((Wff.classMem (Class.cv (nb056_alpha_dummy_023 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_023 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_023 f))).fv) := by
  simpa only [nb056_alpha_dummy_026] using freshVar_not_mem (((Wff.classMem (Class.cv (nb056_alpha_dummy_023 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_023 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_023 f))).fv) 0

theorem nb056_fresh_190 : (nb056_alpha_dummy_061) ∉ (((Wff.classMem (Class.cv (nb056_alpha_dummy_057)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_057)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_057))).fv) := by
  simpa only [nb056_alpha_dummy_061] using freshVar_not_mem (((Wff.classMem (Class.cv (nb056_alpha_dummy_057)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_057)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_057))).fv) 0

theorem nb056_fresh_191 (f : Var) : (nb056_alpha_dummy_062 f) ∉ (((Wff.classMem (Class.cv (nb056_alpha_dummy_059 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_059 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_059 f))).fv) := by
  simpa only [nb056_alpha_dummy_062] using freshVar_not_mem (((Wff.classMem (Class.cv (nb056_alpha_dummy_059 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_059 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_059 f))).fv) 0

theorem nb056_fresh_192 : (nb056_alpha_dummy_103) ∉ (((Wff.classMem (Class.cv (nb056_alpha_dummy_099)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_099)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_099))).fv) := by
  simpa only [nb056_alpha_dummy_103] using freshVar_not_mem (((Wff.classMem (Class.cv (nb056_alpha_dummy_099)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_099)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_099))).fv) 0

theorem nb056_fresh_193 (f : Var) : (nb056_alpha_dummy_104 f) ∉ (((Wff.classMem (Class.cv (nb056_alpha_dummy_101 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_101 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_101 f))).fv) := by
  simpa only [nb056_alpha_dummy_104] using freshVar_not_mem (((Wff.classMem (Class.cv (nb056_alpha_dummy_101 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_101 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_101 f))).fv) 0

theorem nb056_fresh_194 : (nb056_alpha_dummy_139) ∉ (((Wff.classMem (Class.cv (nb056_alpha_dummy_135)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_135)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_135))).fv) := by
  simpa only [nb056_alpha_dummy_139] using freshVar_not_mem (((Wff.classMem (Class.cv (nb056_alpha_dummy_135)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_135)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_135))).fv) 0

theorem nb056_fresh_195 (f : Var) : (nb056_alpha_dummy_140 f) ∉ (((Wff.classMem (Class.cv (nb056_alpha_dummy_137 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_137 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_137 f))).fv) := by
  simpa only [nb056_alpha_dummy_140] using freshVar_not_mem (((Wff.classMem (Class.cv (nb056_alpha_dummy_137 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_137 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_137 f))).fv) 0

theorem nb056_fresh_196 : (nb056_alpha_dummy_175) ∉ (((Wff.classMem (Class.cv (nb056_alpha_dummy_171)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_171)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_171))).fv) := by
  simpa only [nb056_alpha_dummy_175] using freshVar_not_mem (((Wff.classMem (Class.cv (nb056_alpha_dummy_171)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_171)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_171))).fv) 0

theorem nb056_fresh_197 (f : Var) : (nb056_alpha_dummy_176 f) ∉ (((Wff.classMem (Class.cv (nb056_alpha_dummy_173 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_173 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_173 f))).fv) := by
  simpa only [nb056_alpha_dummy_176] using freshVar_not_mem (((Wff.classMem (Class.cv (nb056_alpha_dummy_173 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_173 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_173 f))).fv) 0

theorem nb056_fresh_198 : (nb056_alpha_dummy_003) ∉ (((syn_ccom (Class.cv (nb056_alpha_dummy_000)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb056_alpha_dummy_003] using freshVar_not_mem (((syn_ccom (Class.cv (nb056_alpha_dummy_000)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) 0

theorem nb056_fresh_199 (f : Var) : (nb056_alpha_dummy_004 f) ∉ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb056_alpha_dummy_004] using freshVar_not_mem (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb056_fresh_200 : (nb056_alpha_dummy_017) ∉ (((syn_ccompl (Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb056_alpha_dummy_017] using freshVar_not_mem (((syn_ccompl (Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cphi (Class.cv (nb056_alpha_dummy_014)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb056_fresh_201 (f : Var) : (nb056_alpha_dummy_018 f) ∉ (((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb056_alpha_dummy_018] using freshVar_not_mem (((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb056_fresh_202 : (nb056_alpha_dummy_053) ∉ (((syn_ccompl (Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb056_alpha_dummy_053] using freshVar_not_mem (((syn_ccompl (Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_049) (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb056_fresh_203 (f : Var) : (nb056_alpha_dummy_054 f) ∉ (((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb056_alpha_dummy_054] using freshVar_not_mem (((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f) (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb056_fresh_204 : (nb056_alpha_dummy_095) ∉ (((syn_ccompl (Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cphi (Class.cv (nb056_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb056_alpha_dummy_095] using freshVar_not_mem (((syn_ccompl (Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cphi (Class.cv (nb056_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_091) (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb056_fresh_205 (f : Var) : (nb056_alpha_dummy_096 f) ∉ (((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb056_alpha_dummy_096] using freshVar_not_mem (((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f) (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb056_fresh_206 : (nb056_alpha_dummy_131) ∉ (((syn_ccompl (Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cphi (Class.cv (nb056_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb056_alpha_dummy_131] using freshVar_not_mem (((syn_ccompl (Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cphi (Class.cv (nb056_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb056_fresh_207 (f : Var) : (nb056_alpha_dummy_132 f) ∉ (((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb056_alpha_dummy_132] using freshVar_not_mem (((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb056_fresh_208 : (nb056_alpha_dummy_167) ∉ (((syn_ccompl (Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb056_alpha_dummy_167] using freshVar_not_mem (((syn_ccompl (Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb056_fresh_209 (f : Var) : (nb056_alpha_dummy_168 f) ∉ (((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb056_alpha_dummy_168] using freshVar_not_mem (((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb056_fresh_210 : (nb056_alpha_dummy_037) ∉ (((syn_ccompl (Class.cv (nb056_alpha_dummy_028)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_029)))).fv) := by
  simpa only [nb056_alpha_dummy_037] using freshVar_not_mem (((syn_ccompl (Class.cv (nb056_alpha_dummy_028)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_029)))).fv) 0

theorem nb056_fresh_211 (f : Var) : (nb056_alpha_dummy_038 f) ∉ (((syn_ccompl (Class.cv (nb056_alpha_dummy_031 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_032 f)))).fv) := by
  simpa only [nb056_alpha_dummy_038] using freshVar_not_mem (((syn_ccompl (Class.cv (nb056_alpha_dummy_031 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_032 f)))).fv) 0

theorem nb056_fresh_212 : (nb056_alpha_dummy_073) ∉ (((syn_ccompl (Class.cv (nb056_alpha_dummy_064)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_065)))).fv) := by
  simpa only [nb056_alpha_dummy_073] using freshVar_not_mem (((syn_ccompl (Class.cv (nb056_alpha_dummy_064)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_065)))).fv) 0

theorem nb056_fresh_213 (f : Var) : (nb056_alpha_dummy_074 f) ∉ (((syn_ccompl (Class.cv (nb056_alpha_dummy_067 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_068 f)))).fv) := by
  simpa only [nb056_alpha_dummy_074] using freshVar_not_mem (((syn_ccompl (Class.cv (nb056_alpha_dummy_067 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_068 f)))).fv) 0

theorem nb056_fresh_214 : (nb056_alpha_dummy_115) ∉ (((syn_ccompl (Class.cv (nb056_alpha_dummy_106)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_107)))).fv) := by
  simpa only [nb056_alpha_dummy_115] using freshVar_not_mem (((syn_ccompl (Class.cv (nb056_alpha_dummy_106)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_107)))).fv) 0

theorem nb056_fresh_215 (f : Var) : (nb056_alpha_dummy_116 f) ∉ (((syn_ccompl (Class.cv (nb056_alpha_dummy_109 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_110 f)))).fv) := by
  simpa only [nb056_alpha_dummy_116] using freshVar_not_mem (((syn_ccompl (Class.cv (nb056_alpha_dummy_109 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_110 f)))).fv) 0

theorem nb056_fresh_216 : (nb056_alpha_dummy_151) ∉ (((syn_ccompl (Class.cv (nb056_alpha_dummy_142)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_143)))).fv) := by
  simpa only [nb056_alpha_dummy_151] using freshVar_not_mem (((syn_ccompl (Class.cv (nb056_alpha_dummy_142)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_143)))).fv) 0

theorem nb056_fresh_217 (f : Var) : (nb056_alpha_dummy_152 f) ∉ (((syn_ccompl (Class.cv (nb056_alpha_dummy_145 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_146 f)))).fv) := by
  simpa only [nb056_alpha_dummy_152] using freshVar_not_mem (((syn_ccompl (Class.cv (nb056_alpha_dummy_145 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_146 f)))).fv) 0

theorem nb056_fresh_218 : (nb056_alpha_dummy_187) ∉ (((syn_ccompl (Class.cv (nb056_alpha_dummy_178)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_179)))).fv) := by
  simpa only [nb056_alpha_dummy_187] using freshVar_not_mem (((syn_ccompl (Class.cv (nb056_alpha_dummy_178)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_179)))).fv) 0

theorem nb056_fresh_219 (f : Var) : (nb056_alpha_dummy_188 f) ∉ (((syn_ccompl (Class.cv (nb056_alpha_dummy_181 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_182 f)))).fv) := by
  simpa only [nb056_alpha_dummy_188] using freshVar_not_mem (((syn_ccompl (Class.cv (nb056_alpha_dummy_181 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_182 f)))).fv) 0

theorem nb056_fresh_220 : (nb056_alpha_dummy_045) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_014))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb056_alpha_dummy_045] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_014))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb056_fresh_221 (f : Var) : (nb056_alpha_dummy_046 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb056_alpha_dummy_046] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb056_fresh_222 : (nb056_alpha_dummy_081) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_050))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb056_alpha_dummy_081] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_050))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb056_fresh_223 (f : Var) : (nb056_alpha_dummy_082 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb056_alpha_dummy_082] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb056_fresh_224 : (nb056_alpha_dummy_123) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_092))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb056_alpha_dummy_123] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_092))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb056_fresh_225 (f : Var) : (nb056_alpha_dummy_124 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb056_alpha_dummy_124] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb056_fresh_226 : (nb056_alpha_dummy_159) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_128))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb056_alpha_dummy_159] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_128))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb056_fresh_227 (f : Var) : (nb056_alpha_dummy_160 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb056_alpha_dummy_160] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb056_fresh_228 : (nb056_alpha_dummy_195) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_164))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb056_alpha_dummy_195] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_164))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb056_fresh_229 (f : Var) : (nb056_alpha_dummy_196 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb056_alpha_dummy_196] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb056_fresh_230 : (nb056_alpha_dummy_033) ∉ (((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv) := by
  simpa only [nb056_alpha_dummy_033] using freshVar_not_mem (((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv) 0

theorem nb056_fresh_231 (f : Var) : (nb056_alpha_dummy_034 f) ∉ (((syn_cnin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))).fv) := by
  simpa only [nb056_alpha_dummy_034] using freshVar_not_mem (((syn_cnin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))).fv) 0

theorem nb056_fresh_232 : (nb056_alpha_dummy_069) ∉ (((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv) := by
  simpa only [nb056_alpha_dummy_069] using freshVar_not_mem (((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv) 0

theorem nb056_fresh_233 (f : Var) : (nb056_alpha_dummy_070 f) ∉ (((syn_cnin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))).fv) := by
  simpa only [nb056_alpha_dummy_070] using freshVar_not_mem (((syn_cnin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))).fv) 0

theorem nb056_fresh_234 : (nb056_alpha_dummy_111) ∉ (((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv) := by
  simpa only [nb056_alpha_dummy_111] using freshVar_not_mem (((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv) 0

theorem nb056_fresh_235 (f : Var) : (nb056_alpha_dummy_112 f) ∉ (((syn_cnin (Class.cv (nb056_alpha_dummy_109 f)) (Class.cv (nb056_alpha_dummy_110 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_109 f)) (Class.cv (nb056_alpha_dummy_110 f)))).fv) := by
  simpa only [nb056_alpha_dummy_112] using freshVar_not_mem (((syn_cnin (Class.cv (nb056_alpha_dummy_109 f)) (Class.cv (nb056_alpha_dummy_110 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_109 f)) (Class.cv (nb056_alpha_dummy_110 f)))).fv) 0

theorem nb056_fresh_236 : (nb056_alpha_dummy_147) ∉ (((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv) := by
  simpa only [nb056_alpha_dummy_147] using freshVar_not_mem (((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv) 0

theorem nb056_fresh_237 (f : Var) : (nb056_alpha_dummy_148 f) ∉ (((syn_cnin (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f)))).fv) := by
  simpa only [nb056_alpha_dummy_148] using freshVar_not_mem (((syn_cnin (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f)))).fv) 0

theorem nb056_fresh_238 : (nb056_alpha_dummy_183) ∉ (((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv) := by
  simpa only [nb056_alpha_dummy_183] using freshVar_not_mem (((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv) 0

theorem nb056_fresh_239 (f : Var) : (nb056_alpha_dummy_184 f) ∉ (((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv) := by
  simpa only [nb056_alpha_dummy_184] using freshVar_not_mem (((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv) 0

theorem nb056_fresh_240 : (nb056_alpha_dummy_001) ∉ (((syn_cnin (syn_ccom (Class.cv (nb056_alpha_dummy_000)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb056_alpha_dummy_000)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv) := by
  simpa only [nb056_alpha_dummy_001] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv (nb056_alpha_dummy_000)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb056_alpha_dummy_000)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv) 0

theorem nb056_fresh_241 (f : Var) : (nb056_alpha_dummy_002 f) ∉ (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) := by
  simpa only [nb056_alpha_dummy_002] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0

theorem nb056_fresh_242 : (nb056_alpha_dummy_047) ∉ (((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv) := by
  simpa only [nb056_alpha_dummy_047] using freshVar_not_mem (((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv) 0

theorem nb056_fresh_243 (f : Var) : (nb056_alpha_dummy_048 f) ∉ (((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv) := by
  simpa only [nb056_alpha_dummy_048] using freshVar_not_mem (((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv) 0

theorem nb056_fresh_244 : (nb056_alpha_dummy_083) ∉ (((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv) := by
  simpa only [nb056_alpha_dummy_083] using freshVar_not_mem (((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv) 0

theorem nb056_fresh_245 (f : Var) : (nb056_alpha_dummy_084 f) ∉ (((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv) := by
  simpa only [nb056_alpha_dummy_084] using freshVar_not_mem (((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv) 0

theorem nb056_fresh_246 : (nb056_alpha_dummy_125) ∉ (((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv) := by
  simpa only [nb056_alpha_dummy_125] using freshVar_not_mem (((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv) 0

theorem nb056_fresh_247 (f : Var) : (nb056_alpha_dummy_126 f) ∉ (((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv) := by
  simpa only [nb056_alpha_dummy_126] using freshVar_not_mem (((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv) 0

theorem nb056_fresh_248 : (nb056_alpha_dummy_161) ∉ (((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv) := by
  simpa only [nb056_alpha_dummy_161] using freshVar_not_mem (((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv) 0

theorem nb056_fresh_249 (f : Var) : (nb056_alpha_dummy_162 f) ∉ (((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv) := by
  simpa only [nb056_alpha_dummy_162] using freshVar_not_mem (((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv) 0

theorem nb056_fresh_250 : (nb056_alpha_dummy_197) ∉ (((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv) := by
  simpa only [nb056_alpha_dummy_197] using freshVar_not_mem (((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
