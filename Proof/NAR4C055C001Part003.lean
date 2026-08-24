import NAR4C055C001Part002

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

theorem nb055_fresh_110 : (nb055_alpha_dummy_108) ∉ (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_097))).fv) := by
  simpa only [nb055_alpha_dummy_108] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_097))).fv) 0

theorem nb055_fresh_111 : (nb055_alpha_dummy_104) ∉ (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) := by
  simpa only [nb055_alpha_dummy_104] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_097))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) 0

theorem nb055_fresh_112 : (nb055_alpha_dummy_110) ∉ (((Class.cv (nb055_alpha_dummy_098))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) := by
  simpa only [nb055_alpha_dummy_110] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_098))).fv ∪ ((Class.cv (nb055_alpha_dummy_098))).fv) 0

theorem nb055_fresh_113 (x : Var) (y : Var) : (nb055_alpha_dummy_109 x y) ∉ (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_100 x y))).fv) := by
  simpa only [nb055_alpha_dummy_109] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_100 x y))).fv) 0

theorem nb055_fresh_114 (x : Var) (y : Var) : (nb055_alpha_dummy_105 x y) ∉ (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_101 x y))).fv) := by
  simpa only [nb055_alpha_dummy_105] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_100 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_101 x y))).fv) 0

theorem nb055_fresh_115 (x : Var) (y : Var) : (nb055_alpha_dummy_111 x y) ∉ (((Class.cv (nb055_alpha_dummy_101 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_101 x y))).fv) := by
  simpa only [nb055_alpha_dummy_111] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_101 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_101 x y))).fv) 0

theorem nb055_fresh_116 : (nb055_alpha_dummy_126) ∉ (((Class.cv (nb055_alpha_dummy_119))).fv) := by
  simpa only [nb055_alpha_dummy_126] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_119))).fv) 0

theorem nb055_fresh_117 : (nb055_alpha_dummy_127) ∉ (((Class.cv (nb055_alpha_dummy_119))).fv) := by
  simpa only [nb055_alpha_dummy_127] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_119))).fv) 1

theorem nb055_distinct_118 : (nb055_alpha_dummy_126) ≠ (nb055_alpha_dummy_127) := by
  simpa only [nb055_alpha_dummy_126, nb055_alpha_dummy_127] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_119))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_119 (x : Var) (y : Var) : (nb055_alpha_dummy_128 x y) ∉ (((Class.cv (nb055_alpha_dummy_121 x y))).fv) := by
  simpa only [nb055_alpha_dummy_128] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_121 x y))).fv) 0

theorem nb055_fresh_120 (x : Var) (y : Var) : (nb055_alpha_dummy_129 x y) ∉ (((Class.cv (nb055_alpha_dummy_121 x y))).fv) := by
  simpa only [nb055_alpha_dummy_129] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_121 x y))).fv) 1

theorem nb055_distinct_121 (x : Var) (y : Var) : (nb055_alpha_dummy_128 x y) ≠ (nb055_alpha_dummy_129 x y) := by
  simpa only [nb055_alpha_dummy_128, nb055_alpha_dummy_129] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_121 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_122 : (nb055_alpha_dummy_132) ∉ (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_132] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_123 : (nb055_alpha_dummy_133) ∉ (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_133] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_124 : (nb055_alpha_dummy_134) ∉ (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_134] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_125 : (nb055_alpha_dummy_132) ≠ (nb055_alpha_dummy_133) := by
  simpa only [nb055_alpha_dummy_132, nb055_alpha_dummy_133] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_126 : (nb055_alpha_dummy_132) ≠ (nb055_alpha_dummy_134) := by
  simpa only [nb055_alpha_dummy_132, nb055_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_127 : (nb055_alpha_dummy_133) ≠ (nb055_alpha_dummy_134) := by
  simpa only [nb055_alpha_dummy_133, nb055_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_128 (x : Var) (y : Var) : (nb055_alpha_dummy_135 x y) ∉ (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_135] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_129 (x : Var) (y : Var) : (nb055_alpha_dummy_136 x y) ∉ (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_136] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_130 (x : Var) (y : Var) : (nb055_alpha_dummy_137 x y) ∉ (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_137] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_131 (x : Var) (y : Var) : (nb055_alpha_dummy_135 x y) ≠ (nb055_alpha_dummy_136 x y) := by
  simpa only [nb055_alpha_dummy_135, nb055_alpha_dummy_136] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_132 (x : Var) (y : Var) : (nb055_alpha_dummy_135 x y) ≠ (nb055_alpha_dummy_137 x y) := by
  simpa only [nb055_alpha_dummy_135, nb055_alpha_dummy_137] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_133 (x : Var) (y : Var) : (nb055_alpha_dummy_136 x y) ≠ (nb055_alpha_dummy_137 x y) := by
  simpa only [nb055_alpha_dummy_136, nb055_alpha_dummy_137] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_134 : (nb055_alpha_dummy_144) ∉ (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_133))).fv) := by
  simpa only [nb055_alpha_dummy_144] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_133))).fv) 0

theorem nb055_fresh_135 : (nb055_alpha_dummy_140) ∉ (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) := by
  simpa only [nb055_alpha_dummy_140] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_133))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) 0

theorem nb055_fresh_136 : (nb055_alpha_dummy_146) ∉ (((Class.cv (nb055_alpha_dummy_134))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) := by
  simpa only [nb055_alpha_dummy_146] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_134))).fv ∪ ((Class.cv (nb055_alpha_dummy_134))).fv) 0

theorem nb055_fresh_137 (x : Var) (y : Var) : (nb055_alpha_dummy_145 x y) ∉ (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_136 x y))).fv) := by
  simpa only [nb055_alpha_dummy_145] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_136 x y))).fv) 0

theorem nb055_fresh_138 (x : Var) (y : Var) : (nb055_alpha_dummy_141 x y) ∉ (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_137 x y))).fv) := by
  simpa only [nb055_alpha_dummy_141] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_136 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_137 x y))).fv) 0

theorem nb055_fresh_139 (x : Var) (y : Var) : (nb055_alpha_dummy_147 x y) ∉ (((Class.cv (nb055_alpha_dummy_137 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_137 x y))).fv) := by
  simpa only [nb055_alpha_dummy_147] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_137 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_137 x y))).fv) 0

theorem nb055_fresh_140 : (nb055_alpha_dummy_162) ∉ (((Class.cv (nb055_alpha_dummy_155))).fv) := by
  simpa only [nb055_alpha_dummy_162] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_155))).fv) 0

theorem nb055_fresh_141 : (nb055_alpha_dummy_163) ∉ (((Class.cv (nb055_alpha_dummy_155))).fv) := by
  simpa only [nb055_alpha_dummy_163] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_155))).fv) 1

theorem nb055_distinct_142 : (nb055_alpha_dummy_162) ≠ (nb055_alpha_dummy_163) := by
  simpa only [nb055_alpha_dummy_162, nb055_alpha_dummy_163] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_155))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_143 (x : Var) (y : Var) : (nb055_alpha_dummy_164 x y) ∉ (((Class.cv (nb055_alpha_dummy_157 x y))).fv) := by
  simpa only [nb055_alpha_dummy_164] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_157 x y))).fv) 0

theorem nb055_fresh_144 (x : Var) (y : Var) : (nb055_alpha_dummy_165 x y) ∉ (((Class.cv (nb055_alpha_dummy_157 x y))).fv) := by
  simpa only [nb055_alpha_dummy_165] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_157 x y))).fv) 1

theorem nb055_distinct_145 (x : Var) (y : Var) : (nb055_alpha_dummy_164 x y) ≠ (nb055_alpha_dummy_165 x y) := by
  simpa only [nb055_alpha_dummy_164, nb055_alpha_dummy_165] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_157 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_146 : (nb055_alpha_dummy_168) ∉ (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_168] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_147 : (nb055_alpha_dummy_169) ∉ (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_169] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_148 : (nb055_alpha_dummy_170) ∉ (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_170] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_149 : (nb055_alpha_dummy_168) ≠ (nb055_alpha_dummy_169) := by
  simpa only [nb055_alpha_dummy_168, nb055_alpha_dummy_169] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_150 : (nb055_alpha_dummy_168) ≠ (nb055_alpha_dummy_170) := by
  simpa only [nb055_alpha_dummy_168, nb055_alpha_dummy_170] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_151 : (nb055_alpha_dummy_169) ≠ (nb055_alpha_dummy_170) := by
  simpa only [nb055_alpha_dummy_169, nb055_alpha_dummy_170] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_152 (x : Var) (y : Var) : (nb055_alpha_dummy_171 x y) ∉ (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_171] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb055_fresh_153 (x : Var) (y : Var) : (nb055_alpha_dummy_172 x y) ∉ (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_172] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb055_fresh_154 (x : Var) (y : Var) : (nb055_alpha_dummy_173 x y) ∉ (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb055_alpha_dummy_173] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb055_distinct_155 (x : Var) (y : Var) : (nb055_alpha_dummy_171 x y) ≠ (nb055_alpha_dummy_172 x y) := by
  simpa only [nb055_alpha_dummy_171, nb055_alpha_dummy_172] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_156 (x : Var) (y : Var) : (nb055_alpha_dummy_171 x y) ≠ (nb055_alpha_dummy_173 x y) := by
  simpa only [nb055_alpha_dummy_171, nb055_alpha_dummy_173] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_157 (x : Var) (y : Var) : (nb055_alpha_dummy_172 x y) ≠ (nb055_alpha_dummy_173 x y) := by
  simpa only [nb055_alpha_dummy_172, nb055_alpha_dummy_173] using
    (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_158 : (nb055_alpha_dummy_180) ∉ (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_169))).fv) := by
  simpa only [nb055_alpha_dummy_180] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_169))).fv) 0

theorem nb055_fresh_159 : (nb055_alpha_dummy_176) ∉ (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) := by
  simpa only [nb055_alpha_dummy_176] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_169))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) 0

theorem nb055_fresh_160 : (nb055_alpha_dummy_182) ∉ (((Class.cv (nb055_alpha_dummy_170))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) := by
  simpa only [nb055_alpha_dummy_182] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_170))).fv ∪ ((Class.cv (nb055_alpha_dummy_170))).fv) 0

theorem nb055_fresh_161 (x : Var) (y : Var) : (nb055_alpha_dummy_181 x y) ∉ (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_172 x y))).fv) := by
  simpa only [nb055_alpha_dummy_181] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_172 x y))).fv) 0

theorem nb055_fresh_162 (x : Var) (y : Var) : (nb055_alpha_dummy_177 x y) ∉ (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_173 x y))).fv) := by
  simpa only [nb055_alpha_dummy_177] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_172 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_173 x y))).fv) 0

theorem nb055_fresh_163 (x : Var) (y : Var) : (nb055_alpha_dummy_183 x y) ∉ (((Class.cv (nb055_alpha_dummy_173 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_173 x y))).fv) := by
  simpa only [nb055_alpha_dummy_183] using freshVar_not_mem (((Class.cv (nb055_alpha_dummy_173 x y))).fv ∪ ((Class.cv (nb055_alpha_dummy_173 x y))).fv) 0

theorem nb055_fresh_164 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb055_alpha_dummy_016] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb055_fresh_165 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb055_alpha_dummy_017] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb055_fresh_166 (x : Var) (y : Var) : (nb055_alpha_dummy_079 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb055_alpha_dummy_079] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 2

theorem nb055_distinct_167 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ≠ (nb055_alpha_dummy_017 x y) := by
  simpa only [nb055_alpha_dummy_016, nb055_alpha_dummy_017] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb055_distinct_168 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ≠ (nb055_alpha_dummy_079 x y) := by
  simpa only [nb055_alpha_dummy_016, nb055_alpha_dummy_079] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 2) (by decide))

theorem nb055_distinct_169 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ≠ (nb055_alpha_dummy_079 x y) := by
  simpa only [nb055_alpha_dummy_017, nb055_alpha_dummy_079] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 1) (j := 2) (by decide))

theorem nb055_fresh_170 : (nb055_alpha_dummy_026) ∉ (((Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_022)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_022))).fv) := by
  simpa only [nb055_alpha_dummy_026] using freshVar_not_mem (((Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_022)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_022))).fv) 0

theorem nb055_fresh_171 (x : Var) (y : Var) : (nb055_alpha_dummy_027 x y) ∉ (((Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_024 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_024 x y))).fv) := by
  simpa only [nb055_alpha_dummy_027] using freshVar_not_mem (((Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_024 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_024 x y))).fv) 0

theorem nb055_fresh_172 : (nb055_alpha_dummy_054) ∉ (((Wff.classMem (Class.cv (nb055_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_050))).fv) := by
  simpa only [nb055_alpha_dummy_054] using freshVar_not_mem (((Wff.classMem (Class.cv (nb055_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_050))).fv) 0

theorem nb055_fresh_173 (x : Var) (y : Var) : (nb055_alpha_dummy_055 x y) ∉ (((Wff.classMem (Class.cv (nb055_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_052 x y))).fv) := by
  simpa only [nb055_alpha_dummy_055] using freshVar_not_mem (((Wff.classMem (Class.cv (nb055_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_052 x y))).fv) 0

theorem nb055_fresh_174 : (nb055_alpha_dummy_094) ∉ (((Wff.classMem (Class.cv (nb055_alpha_dummy_090)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_090)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_090))).fv) := by
  simpa only [nb055_alpha_dummy_094] using freshVar_not_mem (((Wff.classMem (Class.cv (nb055_alpha_dummy_090)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_090)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_090))).fv) 0

theorem nb055_fresh_175 (x : Var) (y : Var) : (nb055_alpha_dummy_095 x y) ∉ (((Wff.classMem (Class.cv (nb055_alpha_dummy_092 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_092 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_092 x y))).fv) := by
  simpa only [nb055_alpha_dummy_095] using freshVar_not_mem (((Wff.classMem (Class.cv (nb055_alpha_dummy_092 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_092 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_092 x y))).fv) 0

theorem nb055_fresh_176 : (nb055_alpha_dummy_130) ∉ (((Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_126)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_126))).fv) := by
  simpa only [nb055_alpha_dummy_130] using freshVar_not_mem (((Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_126)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_126))).fv) 0

theorem nb055_fresh_177 (x : Var) (y : Var) : (nb055_alpha_dummy_131 x y) ∉ (((Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_128 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_128 x y))).fv) := by
  simpa only [nb055_alpha_dummy_131] using freshVar_not_mem (((Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_128 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_128 x y))).fv) 0

theorem nb055_fresh_178 : (nb055_alpha_dummy_166) ∉ (((Wff.classMem (Class.cv (nb055_alpha_dummy_162)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_162)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_162))).fv) := by
  simpa only [nb055_alpha_dummy_166] using freshVar_not_mem (((Wff.classMem (Class.cv (nb055_alpha_dummy_162)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_162)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_162))).fv) 0

theorem nb055_fresh_179 (x : Var) (y : Var) : (nb055_alpha_dummy_167 x y) ∉ (((Wff.classMem (Class.cv (nb055_alpha_dummy_164 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_164 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_164 x y))).fv) := by
  simpa only [nb055_alpha_dummy_167] using freshVar_not_mem (((Wff.classMem (Class.cv (nb055_alpha_dummy_164 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb055_alpha_dummy_164 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb055_alpha_dummy_164 x y))).fv) 0

theorem nb055_fresh_180 : (nb055_alpha_dummy_010) ∉ (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb055_alpha_dummy_010] using freshVar_not_mem (((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002)) (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb055_fresh_181 (x : Var) (y : Var) : (nb055_alpha_dummy_011 x y) ∉ (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb055_alpha_dummy_011] using freshVar_not_mem (((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y) (Class.cv (nb055_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb055_fresh_182 : (nb055_alpha_dummy_018) ∉ (((syn_ccompl (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb055_alpha_dummy_018] using freshVar_not_mem (((syn_ccompl (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_000)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cphi (Class.cv (nb055_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb055_fresh_183 (x : Var) (y : Var) : (nb055_alpha_dummy_019 x y) ∉ (((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb055_alpha_dummy_019] using freshVar_not_mem (((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb055_fresh_184 : (nb055_alpha_dummy_086) ∉ (((syn_ccompl (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb055_alpha_dummy_086] using freshVar_not_mem (((syn_ccompl (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cphi (Class.cv (nb055_alpha_dummy_083)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_082) (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_082)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb055_fresh_185 (x : Var) (y : Var) : (nb055_alpha_dummy_087 x y) ∉ (((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb055_alpha_dummy_087] using freshVar_not_mem (((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_084 x y) (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb055_fresh_186 : (nb055_alpha_dummy_122) ∉ (((syn_ccompl (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb055_alpha_dummy_122] using freshVar_not_mem (((syn_ccompl (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_014)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cphi (Class.cv (nb055_alpha_dummy_119)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_118) (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_118)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb055_fresh_187 (x : Var) (y : Var) : (nb055_alpha_dummy_123 x y) ∉ (((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb055_alpha_dummy_123] using freshVar_not_mem (((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_016 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_120 x y) (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb055_fresh_188 : (nb055_alpha_dummy_158) ∉ (((syn_ccompl (Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb055_alpha_dummy_158] using freshVar_not_mem (((syn_ccompl (Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_078)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cphi (Class.cv (nb055_alpha_dummy_155)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_154) (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015)) (Wff.classEq (Class.cv (nb055_alpha_dummy_154)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb055_fresh_189 (x : Var) (y : Var) : (nb055_alpha_dummy_159 x y) ∉ (((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb055_alpha_dummy_159] using freshVar_not_mem (((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_079 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb055_alpha_dummy_156 x y) (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y)) (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb055_fresh_190 : (nb055_alpha_dummy_038) ∉ (((syn_ccompl (Class.cv (nb055_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_030)))).fv) := by
  simpa only [nb055_alpha_dummy_038] using freshVar_not_mem (((syn_ccompl (Class.cv (nb055_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_030)))).fv) 0

theorem nb055_fresh_191 (x : Var) (y : Var) : (nb055_alpha_dummy_039 x y) ∉ (((syn_ccompl (Class.cv (nb055_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_033 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_039] using freshVar_not_mem (((syn_ccompl (Class.cv (nb055_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_033 x y)))).fv) 0

theorem nb055_fresh_192 : (nb055_alpha_dummy_066) ∉ (((syn_ccompl (Class.cv (nb055_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_058)))).fv) := by
  simpa only [nb055_alpha_dummy_066] using freshVar_not_mem (((syn_ccompl (Class.cv (nb055_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_058)))).fv) 0

theorem nb055_fresh_193 (x : Var) (y : Var) : (nb055_alpha_dummy_067 x y) ∉ (((syn_ccompl (Class.cv (nb055_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_061 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_067] using freshVar_not_mem (((syn_ccompl (Class.cv (nb055_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_061 x y)))).fv) 0

theorem nb055_fresh_194 : (nb055_alpha_dummy_106) ∉ (((syn_ccompl (Class.cv (nb055_alpha_dummy_097)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_098)))).fv) := by
  simpa only [nb055_alpha_dummy_106] using freshVar_not_mem (((syn_ccompl (Class.cv (nb055_alpha_dummy_097)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_098)))).fv) 0

theorem nb055_fresh_195 (x : Var) (y : Var) : (nb055_alpha_dummy_107 x y) ∉ (((syn_ccompl (Class.cv (nb055_alpha_dummy_100 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_101 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_107] using freshVar_not_mem (((syn_ccompl (Class.cv (nb055_alpha_dummy_100 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_101 x y)))).fv) 0

theorem nb055_fresh_196 : (nb055_alpha_dummy_142) ∉ (((syn_ccompl (Class.cv (nb055_alpha_dummy_133)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_134)))).fv) := by
  simpa only [nb055_alpha_dummy_142] using freshVar_not_mem (((syn_ccompl (Class.cv (nb055_alpha_dummy_133)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_134)))).fv) 0

theorem nb055_fresh_197 (x : Var) (y : Var) : (nb055_alpha_dummy_143 x y) ∉ (((syn_ccompl (Class.cv (nb055_alpha_dummy_136 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_137 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_143] using freshVar_not_mem (((syn_ccompl (Class.cv (nb055_alpha_dummy_136 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_137 x y)))).fv) 0

theorem nb055_fresh_198 : (nb055_alpha_dummy_178) ∉ (((syn_ccompl (Class.cv (nb055_alpha_dummy_169)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_170)))).fv) := by
  simpa only [nb055_alpha_dummy_178] using freshVar_not_mem (((syn_ccompl (Class.cv (nb055_alpha_dummy_169)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_170)))).fv) 0

theorem nb055_fresh_199 (x : Var) (y : Var) : (nb055_alpha_dummy_179 x y) ∉ (((syn_ccompl (Class.cv (nb055_alpha_dummy_172 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_173 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_179] using freshVar_not_mem (((syn_ccompl (Class.cv (nb055_alpha_dummy_172 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb055_alpha_dummy_173 x y)))).fv) 0

theorem nb055_fresh_200 : (nb055_alpha_dummy_074) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb055_alpha_dummy_074] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb055_fresh_201 (x : Var) (y : Var) : (nb055_alpha_dummy_075 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb055_alpha_dummy_075] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb055_fresh_202 : (nb055_alpha_dummy_046) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_015))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb055_alpha_dummy_046] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_015))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb055_fresh_203 (x : Var) (y : Var) : (nb055_alpha_dummy_047 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb055_alpha_dummy_047] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb055_fresh_204 : (nb055_alpha_dummy_114) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_083))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb055_alpha_dummy_114] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_083))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb055_fresh_205 (x : Var) (y : Var) : (nb055_alpha_dummy_115 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb055_alpha_dummy_115] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb055_fresh_206 : (nb055_alpha_dummy_150) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_119))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb055_alpha_dummy_150] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_119))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb055_fresh_207 (x : Var) (y : Var) : (nb055_alpha_dummy_151 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb055_alpha_dummy_151] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb055_fresh_208 : (nb055_alpha_dummy_186) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_155))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb055_alpha_dummy_186] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_155))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb055_fresh_209 (x : Var) (y : Var) : (nb055_alpha_dummy_187 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb055_alpha_dummy_187] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb055_fresh_210 : (nb055_alpha_dummy_034) ∉ (((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv) := by
  simpa only [nb055_alpha_dummy_034] using freshVar_not_mem (((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))).fv) 0

theorem nb055_fresh_211 (x : Var) (y : Var) : (nb055_alpha_dummy_035 x y) ∉ (((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y)) (Class.cv (nb055_alpha_dummy_033 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y)) (Class.cv (nb055_alpha_dummy_033 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_035] using freshVar_not_mem (((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y)) (Class.cv (nb055_alpha_dummy_033 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_032 x y)) (Class.cv (nb055_alpha_dummy_033 x y)))).fv) 0

theorem nb055_fresh_212 : (nb055_alpha_dummy_062) ∉ (((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv) := by
  simpa only [nb055_alpha_dummy_062] using freshVar_not_mem (((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))).fv) 0

theorem nb055_fresh_213 (x : Var) (y : Var) : (nb055_alpha_dummy_063 x y) ∉ (((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_063] using freshVar_not_mem (((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))).fv) 0

theorem nb055_fresh_214 : (nb055_alpha_dummy_102) ∉ (((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv) := by
  simpa only [nb055_alpha_dummy_102] using freshVar_not_mem (((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))).fv) 0

theorem nb055_fresh_215 (x : Var) (y : Var) : (nb055_alpha_dummy_103 x y) ∉ (((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y)) (Class.cv (nb055_alpha_dummy_101 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y)) (Class.cv (nb055_alpha_dummy_101 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_103] using freshVar_not_mem (((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y)) (Class.cv (nb055_alpha_dummy_101 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_100 x y)) (Class.cv (nb055_alpha_dummy_101 x y)))).fv) 0

theorem nb055_fresh_216 : (nb055_alpha_dummy_138) ∉ (((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv) := by
  simpa only [nb055_alpha_dummy_138] using freshVar_not_mem (((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))).fv) 0

theorem nb055_fresh_217 (x : Var) (y : Var) : (nb055_alpha_dummy_139 x y) ∉ (((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_139] using freshVar_not_mem (((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_136 x y)) (Class.cv (nb055_alpha_dummy_137 x y)))).fv) 0

theorem nb055_fresh_218 : (nb055_alpha_dummy_174) ∉ (((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv) := by
  simpa only [nb055_alpha_dummy_174] using freshVar_not_mem (((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))).fv) 0

theorem nb055_fresh_219 (x : Var) (y : Var) : (nb055_alpha_dummy_175 x y) ∉ (((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_175] using freshVar_not_mem (((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))).fv ∪ ((syn_cnin (Class.cv (nb055_alpha_dummy_172 x y)) (Class.cv (nb055_alpha_dummy_173 x y)))).fv) 0

theorem nb055_fresh_220 : (nb055_alpha_dummy_006) ∉ (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) := by
  simpa only [nb055_alpha_dummy_006] using freshVar_not_mem (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) 0

theorem nb055_fresh_221 : (nb055_alpha_dummy_007) ∉ (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) := by
  simpa only [nb055_alpha_dummy_007] using freshVar_not_mem (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) 1

theorem nb055_distinct_222 : (nb055_alpha_dummy_006) ≠ (nb055_alpha_dummy_007) := by
  simpa only [nb055_alpha_dummy_006, nb055_alpha_dummy_007] using
    (freshVar_injective (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_223 (x : Var) (y : Var) : (nb055_alpha_dummy_008 x y) ∉ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) := by
  simpa only [nb055_alpha_dummy_008] using freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) 0

theorem nb055_fresh_224 (x : Var) (y : Var) : (nb055_alpha_dummy_009 x y) ∉ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) := by
  simpa only [nb055_alpha_dummy_009] using freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) 1

theorem nb055_distinct_225 (x : Var) (y : Var) : (nb055_alpha_dummy_008 x y) ≠ (nb055_alpha_dummy_009 x y) := by
  simpa only [nb055_alpha_dummy_008, nb055_alpha_dummy_009] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb055_fresh_226 : (nb055_alpha_dummy_076) ∉ (((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv) := by
  simpa only [nb055_alpha_dummy_076] using freshVar_not_mem (((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_007)))).fv) 0

theorem nb055_fresh_227 (x : Var) (y : Var) : (nb055_alpha_dummy_077 x y) ∉ (((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_077] using freshVar_not_mem (((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))).fv) 0

theorem nb055_fresh_228 : (nb055_alpha_dummy_048) ∉ (((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv) := by
  simpa only [nb055_alpha_dummy_048] using freshVar_not_mem (((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_015)))).fv) 0

theorem nb055_fresh_229 (x : Var) (y : Var) : (nb055_alpha_dummy_049 x y) ∉ (((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_049] using freshVar_not_mem (((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))).fv) 0

theorem nb055_fresh_230 : (nb055_alpha_dummy_116) ∉ (((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv) := by
  simpa only [nb055_alpha_dummy_116] using freshVar_not_mem (((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_083)))).fv) 0

theorem nb055_fresh_231 (x : Var) (y : Var) : (nb055_alpha_dummy_117 x y) ∉ (((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_117] using freshVar_not_mem (((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))).fv) 0

theorem nb055_fresh_232 : (nb055_alpha_dummy_152) ∉ (((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv) := by
  simpa only [nb055_alpha_dummy_152] using freshVar_not_mem (((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_119)))).fv) 0

theorem nb055_fresh_233 (x : Var) (y : Var) : (nb055_alpha_dummy_153 x y) ∉ (((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_153] using freshVar_not_mem (((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))).fv) 0

theorem nb055_fresh_234 : (nb055_alpha_dummy_188) ∉ (((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv) := by
  simpa only [nb055_alpha_dummy_188] using freshVar_not_mem (((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_155)))).fv) 0

theorem nb055_fresh_235 (x : Var) (y : Var) : (nb055_alpha_dummy_189 x y) ∉ (((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv) := by
  simpa only [nb055_alpha_dummy_189] using freshVar_not_mem (((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv ∪ ((syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))).fv) 0

theorem nb055_fresh_236 : (nb055_alpha_dummy_002) ∉ (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv) := by
  simpa only [nb055_alpha_dummy_002] using freshVar_not_mem (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv) 0

theorem nb055_fresh_237 : (nb055_alpha_dummy_004) ∉ (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_002)) (syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))))).fv) := by
  simpa only [nb055_alpha_dummy_004] using freshVar_not_mem (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_002)) (syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))))).fv) 0

theorem nb055_fresh_238 : (nb055_alpha_dummy_080) ∉ (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014)) (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078))) (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_015)))))).fv) := by
  simpa only [nb055_alpha_dummy_080] using freshVar_not_mem (({(nb055_alpha_dummy_014)} : Finset Var) ∪ ({(nb055_alpha_dummy_015)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_078) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_014)) (Class.cv (nb055_alpha_dummy_001)) (Class.cv (nb055_alpha_dummy_078))) (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_015)))))).fv) 0

theorem nb055_fresh_239 (x : Var) (y : Var) : (nb055_alpha_dummy_081 x y) ∉ (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y) (Class.cv (nb055_alpha_dummy_079 x y))) (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x) (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) := by
  simpa only [nb055_alpha_dummy_081] using freshVar_not_mem (({(nb055_alpha_dummy_016 x y)} : Finset Var) ∪ ({(nb055_alpha_dummy_017 x y)} : Finset Var) ∪ ((syn_wex (nb055_alpha_dummy_079 x y) (syn_wa (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y) (Class.cv (nb055_alpha_dummy_079 x y))) (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x) (Class.cv (nb055_alpha_dummy_017 x y)))))).fv) 0

theorem nb055_fresh_240 (x : Var) (y : Var) : (nb055_alpha_dummy_003 x y) ∉ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_ccom (Class.cv x) (Class.cv y))).fv) := by
  simpa only [nb055_alpha_dummy_003] using freshVar_not_mem (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_ccom (Class.cv x) (Class.cv y))).fv) 0

theorem nb055_fresh_241 (x : Var) (y : Var) : (nb055_alpha_dummy_005 x y) ∉ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y)) (syn_ccom (Class.cv x) (Class.cv y))))).fv) := by
  simpa only [nb055_alpha_dummy_005] using freshVar_not_mem (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y)) (syn_ccom (Class.cv x) (Class.cv y))))).fv) 0

theorem nb055_fresh_242 : (nb055_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb055_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb055_fresh_243 : (nb055_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb055_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb055_distinct_244 : (nb055_alpha_dummy_000) ≠ (nb055_alpha_dummy_001) := by
  simpa only [nb055_alpha_dummy_000, nb055_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb055_support_mem_0000 : (nb055_alpha_dummy_000) ∈ (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_002)) (syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0001 (x : Var) (y : Var) : x ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y)) (syn_ccom (Class.cv x) (Class.cv y))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0002 : (nb055_alpha_dummy_001) ∈ (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_002)) (syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0003 (x : Var) (y : Var) : y ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y)) (syn_ccom (Class.cv x) (Class.cv y))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0004 : (nb055_alpha_dummy_002) ∈ (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ({(nb055_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_002)) (syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0005 (x : Var) (y : Var) : (nb055_alpha_dummy_003 x y) ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb055_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y)) (syn_ccom (Class.cv x) (Class.cv y))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0006 : (nb055_alpha_dummy_000) ∈ (({(nb055_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb055_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_ccom (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0007 (x : Var) (y : Var) : x ∈ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_ccom (Class.cv x) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb055_support_mem_0008 : (nb055_alpha_dummy_000) ∈ (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
