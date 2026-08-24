import NAR4C090C001Part008

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

theorem nb090_fresh_242 (A : Class) : (nb090_alpha_dummy_107 A) ∉ (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_107] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_243 (A : Class) : (nb090_alpha_dummy_108 A) ∉ (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_108] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_244 (A : Class) : (nb090_alpha_dummy_109 A) ∉ (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_109] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_245 (A : Class) : (nb090_alpha_dummy_107 A) ≠ (nb090_alpha_dummy_108 A) := by
  simpa only [nb090_alpha_dummy_107, nb090_alpha_dummy_108] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_246 (A : Class) : (nb090_alpha_dummy_107 A) ≠ (nb090_alpha_dummy_109 A) := by
  simpa only [nb090_alpha_dummy_107, nb090_alpha_dummy_109] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_247 (A : Class) : (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_109 A) := by
  simpa only [nb090_alpha_dummy_108, nb090_alpha_dummy_109] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_248 (h : Var) : (nb090_alpha_dummy_110 h) ∉ (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_110] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_249 (h : Var) : (nb090_alpha_dummy_111 h) ∉ (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_111] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_250 (h : Var) : (nb090_alpha_dummy_112 h) ∉ (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_112] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_251 (h : Var) : (nb090_alpha_dummy_110 h) ≠ (nb090_alpha_dummy_111 h) := by
  simpa only [nb090_alpha_dummy_110, nb090_alpha_dummy_111] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_252 (h : Var) : (nb090_alpha_dummy_110 h) ≠ (nb090_alpha_dummy_112 h) := by
  simpa only [nb090_alpha_dummy_110, nb090_alpha_dummy_112] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_253 (h : Var) : (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_112 h) := by
  simpa only [nb090_alpha_dummy_111, nb090_alpha_dummy_112] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_254 (A : Class) : (nb090_alpha_dummy_119 A) ∉ (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_108 A))).fv) := by
  simpa only [nb090_alpha_dummy_119] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_108 A))).fv) 0

theorem nb090_fresh_255 (A : Class) : (nb090_alpha_dummy_115 A) ∉ (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) := by
  simpa only [nb090_alpha_dummy_115] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) 0

theorem nb090_fresh_256 (A : Class) : (nb090_alpha_dummy_121 A) ∉ (((Class.cv (nb090_alpha_dummy_109 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) := by
  simpa only [nb090_alpha_dummy_121] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_109 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) 0

theorem nb090_fresh_257 (h : Var) : (nb090_alpha_dummy_120 h) ∉ (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_111 h))).fv) := by
  simpa only [nb090_alpha_dummy_120] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_111 h))).fv) 0

theorem nb090_fresh_258 (h : Var) : (nb090_alpha_dummy_116 h) ∉ (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) := by
  simpa only [nb090_alpha_dummy_116] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) 0

theorem nb090_fresh_259 (h : Var) : (nb090_alpha_dummy_122 h) ∉ (((Class.cv (nb090_alpha_dummy_112 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) := by
  simpa only [nb090_alpha_dummy_122] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_112 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) 0

theorem nb090_fresh_260 (A : Class) : (nb090_alpha_dummy_135 A) ∉ (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) := by
  simpa only [nb090_alpha_dummy_135] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) 0

theorem nb090_fresh_261 (A : Class) : (nb090_alpha_dummy_136 A) ∉ (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) := by
  simpa only [nb090_alpha_dummy_136] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) 1

theorem nb090_distinct_262 (A : Class) : (nb090_alpha_dummy_135 A) ≠ (nb090_alpha_dummy_136 A) := by
  simpa only [nb090_alpha_dummy_135, nb090_alpha_dummy_136] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_263 (A : Class) : (nb090_alpha_dummy_171 A) ∉ (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) := by
  simpa only [nb090_alpha_dummy_171] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) 0

theorem nb090_fresh_264 (A : Class) : (nb090_alpha_dummy_172 A) ∉ (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) := by
  simpa only [nb090_alpha_dummy_172] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) 1

theorem nb090_distinct_265 (A : Class) : (nb090_alpha_dummy_171 A) ≠ (nb090_alpha_dummy_172 A) := by
  simpa only [nb090_alpha_dummy_171, nb090_alpha_dummy_172] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_266 (h : Var) : (nb090_alpha_dummy_137 h) ∉ (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) := by
  simpa only [nb090_alpha_dummy_137] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) 0

theorem nb090_fresh_267 (h : Var) : (nb090_alpha_dummy_138 h) ∉ (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) := by
  simpa only [nb090_alpha_dummy_138] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) 1

theorem nb090_distinct_268 (h : Var) : (nb090_alpha_dummy_137 h) ≠ (nb090_alpha_dummy_138 h) := by
  simpa only [nb090_alpha_dummy_137, nb090_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_269 (h : Var) : (nb090_alpha_dummy_173 h) ∉ (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) := by
  simpa only [nb090_alpha_dummy_173] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) 0

theorem nb090_fresh_270 (h : Var) : (nb090_alpha_dummy_174 h) ∉ (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) := by
  simpa only [nb090_alpha_dummy_174] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) 1

theorem nb090_distinct_271 (h : Var) : (nb090_alpha_dummy_173 h) ≠ (nb090_alpha_dummy_174 h) := by
  simpa only [nb090_alpha_dummy_173, nb090_alpha_dummy_174] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_272 (A : Class) : (nb090_alpha_dummy_143 A) ∉ (((Class.cv (nb090_alpha_dummy_136 A))).fv) := by
  simpa only [nb090_alpha_dummy_143] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_136 A))).fv) 0

theorem nb090_fresh_273 (A : Class) : (nb090_alpha_dummy_144 A) ∉ (((Class.cv (nb090_alpha_dummy_136 A))).fv) := by
  simpa only [nb090_alpha_dummy_144] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_136 A))).fv) 1

theorem nb090_distinct_274 (A : Class) : (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_144 A) := by
  simpa only [nb090_alpha_dummy_143, nb090_alpha_dummy_144] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_275 (h : Var) : (nb090_alpha_dummy_145 h) ∉ (((Class.cv (nb090_alpha_dummy_138 h))).fv) := by
  simpa only [nb090_alpha_dummy_145] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_138 h))).fv) 0

theorem nb090_fresh_276 (h : Var) : (nb090_alpha_dummy_146 h) ∉ (((Class.cv (nb090_alpha_dummy_138 h))).fv) := by
  simpa only [nb090_alpha_dummy_146] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_138 h))).fv) 1

theorem nb090_distinct_277 (h : Var) : (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_146 h) := by
  simpa only [nb090_alpha_dummy_145, nb090_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_278 (A : Class) : (nb090_alpha_dummy_149 A) ∉ (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_149] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_279 (A : Class) : (nb090_alpha_dummy_150 A) ∉ (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_150] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_280 (A : Class) : (nb090_alpha_dummy_151 A) ∉ (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_151] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_281 (A : Class) : (nb090_alpha_dummy_149 A) ≠ (nb090_alpha_dummy_150 A) := by
  simpa only [nb090_alpha_dummy_149, nb090_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_282 (A : Class) : (nb090_alpha_dummy_149 A) ≠ (nb090_alpha_dummy_151 A) := by
  simpa only [nb090_alpha_dummy_149, nb090_alpha_dummy_151] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_283 (A : Class) : (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_151 A) := by
  simpa only [nb090_alpha_dummy_150, nb090_alpha_dummy_151] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_284 (h : Var) : (nb090_alpha_dummy_152 h) ∉ (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_152] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_285 (h : Var) : (nb090_alpha_dummy_153 h) ∉ (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_153] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_286 (h : Var) : (nb090_alpha_dummy_154 h) ∉ (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_154] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_287 (h : Var) : (nb090_alpha_dummy_152 h) ≠ (nb090_alpha_dummy_153 h) := by
  simpa only [nb090_alpha_dummy_152, nb090_alpha_dummy_153] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_288 (h : Var) : (nb090_alpha_dummy_152 h) ≠ (nb090_alpha_dummy_154 h) := by
  simpa only [nb090_alpha_dummy_152, nb090_alpha_dummy_154] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_289 (h : Var) : (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_154 h) := by
  simpa only [nb090_alpha_dummy_153, nb090_alpha_dummy_154] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_290 (A : Class) : (nb090_alpha_dummy_161 A) ∉ (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_150 A))).fv) := by
  simpa only [nb090_alpha_dummy_161] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_150 A))).fv) 0

theorem nb090_fresh_291 (A : Class) : (nb090_alpha_dummy_157 A) ∉ (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) := by
  simpa only [nb090_alpha_dummy_157] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) 0

theorem nb090_fresh_292 (A : Class) : (nb090_alpha_dummy_163 A) ∉ (((Class.cv (nb090_alpha_dummy_151 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) := by
  simpa only [nb090_alpha_dummy_163] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_151 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) 0

theorem nb090_fresh_293 (h : Var) : (nb090_alpha_dummy_162 h) ∉ (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_153 h))).fv) := by
  simpa only [nb090_alpha_dummy_162] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_153 h))).fv) 0

theorem nb090_fresh_294 (h : Var) : (nb090_alpha_dummy_158 h) ∉ (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) := by
  simpa only [nb090_alpha_dummy_158] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) 0

theorem nb090_fresh_295 (h : Var) : (nb090_alpha_dummy_164 h) ∉ (((Class.cv (nb090_alpha_dummy_154 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) := by
  simpa only [nb090_alpha_dummy_164] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_154 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) 0

theorem nb090_fresh_296 (A : Class) : (nb090_alpha_dummy_179 A) ∉ (((Class.cv (nb090_alpha_dummy_172 A))).fv) := by
  simpa only [nb090_alpha_dummy_179] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_172 A))).fv) 0

theorem nb090_fresh_297 (A : Class) : (nb090_alpha_dummy_180 A) ∉ (((Class.cv (nb090_alpha_dummy_172 A))).fv) := by
  simpa only [nb090_alpha_dummy_180] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_172 A))).fv) 1

theorem nb090_distinct_298 (A : Class) : (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_180 A) := by
  simpa only [nb090_alpha_dummy_179, nb090_alpha_dummy_180] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_172 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_299 (h : Var) : (nb090_alpha_dummy_181 h) ∉ (((Class.cv (nb090_alpha_dummy_174 h))).fv) := by
  simpa only [nb090_alpha_dummy_181] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_174 h))).fv) 0

theorem nb090_fresh_300 (h : Var) : (nb090_alpha_dummy_182 h) ∉ (((Class.cv (nb090_alpha_dummy_174 h))).fv) := by
  simpa only [nb090_alpha_dummy_182] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_174 h))).fv) 1

theorem nb090_distinct_301 (h : Var) : (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_182 h) := by
  simpa only [nb090_alpha_dummy_181, nb090_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_174 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_302 (A : Class) : (nb090_alpha_dummy_185 A) ∉ (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_185] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_303 (A : Class) : (nb090_alpha_dummy_186 A) ∉ (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_186] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_304 (A : Class) : (nb090_alpha_dummy_187 A) ∉ (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_187] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_305 (A : Class) : (nb090_alpha_dummy_185 A) ≠ (nb090_alpha_dummy_186 A) := by
  simpa only [nb090_alpha_dummy_185, nb090_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_306 (A : Class) : (nb090_alpha_dummy_185 A) ≠ (nb090_alpha_dummy_187 A) := by
  simpa only [nb090_alpha_dummy_185, nb090_alpha_dummy_187] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_307 (A : Class) : (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_187 A) := by
  simpa only [nb090_alpha_dummy_186, nb090_alpha_dummy_187] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_308 (h : Var) : (nb090_alpha_dummy_188 h) ∉ (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_188] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_309 (h : Var) : (nb090_alpha_dummy_189 h) ∉ (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_189] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_310 (h : Var) : (nb090_alpha_dummy_190 h) ∉ (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_190] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_311 (h : Var) : (nb090_alpha_dummy_188 h) ≠ (nb090_alpha_dummy_189 h) := by
  simpa only [nb090_alpha_dummy_188, nb090_alpha_dummy_189] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_312 (h : Var) : (nb090_alpha_dummy_188 h) ≠ (nb090_alpha_dummy_190 h) := by
  simpa only [nb090_alpha_dummy_188, nb090_alpha_dummy_190] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_313 (h : Var) : (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_190 h) := by
  simpa only [nb090_alpha_dummy_189, nb090_alpha_dummy_190] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_314 (A : Class) : (nb090_alpha_dummy_197 A) ∉ (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_186 A))).fv) := by
  simpa only [nb090_alpha_dummy_197] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_186 A))).fv) 0

theorem nb090_fresh_315 (A : Class) : (nb090_alpha_dummy_193 A) ∉ (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) := by
  simpa only [nb090_alpha_dummy_193] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) 0

theorem nb090_fresh_316 (A : Class) : (nb090_alpha_dummy_199 A) ∉ (((Class.cv (nb090_alpha_dummy_187 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) := by
  simpa only [nb090_alpha_dummy_199] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_187 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) 0

theorem nb090_fresh_317 (h : Var) : (nb090_alpha_dummy_198 h) ∉ (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_189 h))).fv) := by
  simpa only [nb090_alpha_dummy_198] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_189 h))).fv) 0

theorem nb090_fresh_318 (h : Var) : (nb090_alpha_dummy_194 h) ∉ (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) := by
  simpa only [nb090_alpha_dummy_194] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) 0

theorem nb090_fresh_319 (h : Var) : (nb090_alpha_dummy_200 h) ∉ (((Class.cv (nb090_alpha_dummy_190 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) := by
  simpa only [nb090_alpha_dummy_200] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_190 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) 0

theorem nb090_fresh_320 (A : Class) : (nb090_alpha_dummy_215 A) ∉ (((Class.cv (nb090_alpha_dummy_208 A))).fv) := by
  simpa only [nb090_alpha_dummy_215] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_208 A))).fv) 0

theorem nb090_fresh_321 (A : Class) : (nb090_alpha_dummy_216 A) ∉ (((Class.cv (nb090_alpha_dummy_208 A))).fv) := by
  simpa only [nb090_alpha_dummy_216] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_208 A))).fv) 1

theorem nb090_distinct_322 (A : Class) : (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_216 A) := by
  simpa only [nb090_alpha_dummy_215, nb090_alpha_dummy_216] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_208 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_323 (h : Var) : (nb090_alpha_dummy_217 h) ∉ (((Class.cv (nb090_alpha_dummy_210 h))).fv) := by
  simpa only [nb090_alpha_dummy_217] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_210 h))).fv) 0

theorem nb090_fresh_324 (h : Var) : (nb090_alpha_dummy_218 h) ∉ (((Class.cv (nb090_alpha_dummy_210 h))).fv) := by
  simpa only [nb090_alpha_dummy_218] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_210 h))).fv) 1

theorem nb090_distinct_325 (h : Var) : (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_218 h) := by
  simpa only [nb090_alpha_dummy_217, nb090_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_210 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_326 (A : Class) : (nb090_alpha_dummy_221 A) ∉ (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_221] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_327 (A : Class) : (nb090_alpha_dummy_222 A) ∉ (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_222] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_328 (A : Class) : (nb090_alpha_dummy_223 A) ∉ (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_223] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_329 (A : Class) : (nb090_alpha_dummy_221 A) ≠ (nb090_alpha_dummy_222 A) := by
  simpa only [nb090_alpha_dummy_221, nb090_alpha_dummy_222] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_330 (A : Class) : (nb090_alpha_dummy_221 A) ≠ (nb090_alpha_dummy_223 A) := by
  simpa only [nb090_alpha_dummy_221, nb090_alpha_dummy_223] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_331 (A : Class) : (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_223 A) := by
  simpa only [nb090_alpha_dummy_222, nb090_alpha_dummy_223] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_332 (h : Var) : (nb090_alpha_dummy_224 h) ∉ (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_224] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_333 (h : Var) : (nb090_alpha_dummy_225 h) ∉ (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_225] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_334 (h : Var) : (nb090_alpha_dummy_226 h) ∉ (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_226] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_335 (h : Var) : (nb090_alpha_dummy_224 h) ≠ (nb090_alpha_dummy_225 h) := by
  simpa only [nb090_alpha_dummy_224, nb090_alpha_dummy_225] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_336 (h : Var) : (nb090_alpha_dummy_224 h) ≠ (nb090_alpha_dummy_226 h) := by
  simpa only [nb090_alpha_dummy_224, nb090_alpha_dummy_226] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_337 (h : Var) : (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_226 h) := by
  simpa only [nb090_alpha_dummy_225, nb090_alpha_dummy_226] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_338 (A : Class) : (nb090_alpha_dummy_233 A) ∉ (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_222 A))).fv) := by
  simpa only [nb090_alpha_dummy_233] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_222 A))).fv) 0

theorem nb090_fresh_339 (A : Class) : (nb090_alpha_dummy_229 A) ∉ (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) := by
  simpa only [nb090_alpha_dummy_229] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) 0

theorem nb090_fresh_340 (A : Class) : (nb090_alpha_dummy_235 A) ∉ (((Class.cv (nb090_alpha_dummy_223 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) := by
  simpa only [nb090_alpha_dummy_235] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_223 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) 0

theorem nb090_fresh_341 (h : Var) : (nb090_alpha_dummy_234 h) ∉ (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_225 h))).fv) := by
  simpa only [nb090_alpha_dummy_234] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_225 h))).fv) 0

theorem nb090_fresh_342 (h : Var) : (nb090_alpha_dummy_230 h) ∉ (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) := by
  simpa only [nb090_alpha_dummy_230] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) 0

theorem nb090_fresh_343 (h : Var) : (nb090_alpha_dummy_236 h) ∉ (((Class.cv (nb090_alpha_dummy_226 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) := by
  simpa only [nb090_alpha_dummy_236] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_226 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) 0

theorem nb090_fresh_344 (A : Class) : (nb090_alpha_dummy_247 A) ∉ (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) := by
  simpa only [nb090_alpha_dummy_247] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) 0

theorem nb090_fresh_345 (A : Class) : (nb090_alpha_dummy_248 A) ∉ (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) := by
  simpa only [nb090_alpha_dummy_248] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) 1

theorem nb090_distinct_346 (A : Class) : (nb090_alpha_dummy_247 A) ≠ (nb090_alpha_dummy_248 A) := by
  simpa only [nb090_alpha_dummy_247, nb090_alpha_dummy_248] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_347 (h : Var) : (nb090_alpha_dummy_249 h) ∉ (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) := by
  simpa only [nb090_alpha_dummy_249] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) 0

theorem nb090_fresh_348 (h : Var) : (nb090_alpha_dummy_250 h) ∉ (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) := by
  simpa only [nb090_alpha_dummy_250] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) 1

theorem nb090_distinct_349 (h : Var) : (nb090_alpha_dummy_249 h) ≠ (nb090_alpha_dummy_250 h) := by
  simpa only [nb090_alpha_dummy_249, nb090_alpha_dummy_250] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_350 (A : Class) : (nb090_alpha_dummy_255 A) ∉ (((Class.cv (nb090_alpha_dummy_248 A))).fv) := by
  simpa only [nb090_alpha_dummy_255] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_248 A))).fv) 0

theorem nb090_fresh_351 (A : Class) : (nb090_alpha_dummy_256 A) ∉ (((Class.cv (nb090_alpha_dummy_248 A))).fv) := by
  simpa only [nb090_alpha_dummy_256] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_248 A))).fv) 1

theorem nb090_distinct_352 (A : Class) : (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_256 A) := by
  simpa only [nb090_alpha_dummy_255, nb090_alpha_dummy_256] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_248 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_353 (h : Var) : (nb090_alpha_dummy_257 h) ∉ (((Class.cv (nb090_alpha_dummy_250 h))).fv) := by
  simpa only [nb090_alpha_dummy_257] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_250 h))).fv) 0

theorem nb090_fresh_354 (h : Var) : (nb090_alpha_dummy_258 h) ∉ (((Class.cv (nb090_alpha_dummy_250 h))).fv) := by
  simpa only [nb090_alpha_dummy_258] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_250 h))).fv) 1

theorem nb090_distinct_355 (h : Var) : (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_258 h) := by
  simpa only [nb090_alpha_dummy_257, nb090_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_250 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_356 (A : Class) : (nb090_alpha_dummy_261 A) ∉ (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_261] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_357 (A : Class) : (nb090_alpha_dummy_262 A) ∉ (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_262] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_358 (A : Class) : (nb090_alpha_dummy_263 A) ∉ (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_263] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_359 (A : Class) : (nb090_alpha_dummy_261 A) ≠ (nb090_alpha_dummy_262 A) := by
  simpa only [nb090_alpha_dummy_261, nb090_alpha_dummy_262] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_360 (A : Class) : (nb090_alpha_dummy_261 A) ≠ (nb090_alpha_dummy_263 A) := by
  simpa only [nb090_alpha_dummy_261, nb090_alpha_dummy_263] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_361 (A : Class) : (nb090_alpha_dummy_262 A) ≠ (nb090_alpha_dummy_263 A) := by
  simpa only [nb090_alpha_dummy_262, nb090_alpha_dummy_263] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_362 (h : Var) : (nb090_alpha_dummy_264 h) ∉ (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_264] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_363 (h : Var) : (nb090_alpha_dummy_265 h) ∉ (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_265] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_364 (h : Var) : (nb090_alpha_dummy_266 h) ∉ (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_266] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_365 (h : Var) : (nb090_alpha_dummy_264 h) ≠ (nb090_alpha_dummy_265 h) := by
  simpa only [nb090_alpha_dummy_264, nb090_alpha_dummy_265] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_366 (h : Var) : (nb090_alpha_dummy_264 h) ≠ (nb090_alpha_dummy_266 h) := by
  simpa only [nb090_alpha_dummy_264, nb090_alpha_dummy_266] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_367 (h : Var) : (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_266 h) := by
  simpa only [nb090_alpha_dummy_265, nb090_alpha_dummy_266] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_368 (A : Class) : (nb090_alpha_dummy_273 A) ∉ (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_262 A))).fv) := by
  simpa only [nb090_alpha_dummy_273] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_262 A))).fv) 0

theorem nb090_fresh_369 (A : Class) : (nb090_alpha_dummy_269 A) ∉ (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) := by
  simpa only [nb090_alpha_dummy_269] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) 0

theorem nb090_fresh_370 (A : Class) : (nb090_alpha_dummy_275 A) ∉ (((Class.cv (nb090_alpha_dummy_263 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) := by
  simpa only [nb090_alpha_dummy_275] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_263 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) 0

theorem nb090_fresh_371 (h : Var) : (nb090_alpha_dummy_274 h) ∉ (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_265 h))).fv) := by
  simpa only [nb090_alpha_dummy_274] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_265 h))).fv) 0

theorem nb090_fresh_372 (h : Var) : (nb090_alpha_dummy_270 h) ∉ (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) := by
  simpa only [nb090_alpha_dummy_270] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) 0

theorem nb090_fresh_373 (h : Var) : (nb090_alpha_dummy_276 h) ∉ (((Class.cv (nb090_alpha_dummy_266 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) := by
  simpa only [nb090_alpha_dummy_276] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_266 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) 0

theorem nb090_fresh_374 (A : Class) : (nb090_alpha_dummy_327 A) ∉ (((Class.cv (nb090_alpha_dummy_285 A))).fv) := by
  simpa only [nb090_alpha_dummy_327] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_285 A))).fv) 0

theorem nb090_fresh_375 (u : Var) : (nb090_alpha_dummy_328 u) ∉ (((Class.cv (nb090_alpha_dummy_286 u))).fv) := by
  simpa only [nb090_alpha_dummy_328] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_286 u))).fv) 0

theorem nb090_fresh_376 (A : Class) : (nb090_alpha_dummy_299 A) ∉ (((Class.cv (nb090_alpha_dummy_292 A))).fv) := by
  simpa only [nb090_alpha_dummy_299] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_292 A))).fv) 0

theorem nb090_fresh_377 (A : Class) : (nb090_alpha_dummy_300 A) ∉ (((Class.cv (nb090_alpha_dummy_292 A))).fv) := by
  simpa only [nb090_alpha_dummy_300] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_292 A))).fv) 1

theorem nb090_distinct_378 (A : Class) : (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_300 A) := by
  simpa only [nb090_alpha_dummy_299, nb090_alpha_dummy_300] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_292 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_379 (u : Var) : (nb090_alpha_dummy_301 u) ∉ (((Class.cv (nb090_alpha_dummy_294 u))).fv) := by
  simpa only [nb090_alpha_dummy_301] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_294 u))).fv) 0

theorem nb090_fresh_380 (u : Var) : (nb090_alpha_dummy_302 u) ∉ (((Class.cv (nb090_alpha_dummy_294 u))).fv) := by
  simpa only [nb090_alpha_dummy_302] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_294 u))).fv) 1

theorem nb090_distinct_381 (u : Var) : (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_302 u) := by
  simpa only [nb090_alpha_dummy_301, nb090_alpha_dummy_302] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_294 u))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_382 (A : Class) : (nb090_alpha_dummy_305 A) ∉ (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_305] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_383 (A : Class) : (nb090_alpha_dummy_306 A) ∉ (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_306] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_384 (A : Class) : (nb090_alpha_dummy_307 A) ∉ (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_307] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_385 (A : Class) : (nb090_alpha_dummy_305 A) ≠ (nb090_alpha_dummy_306 A) := by
  simpa only [nb090_alpha_dummy_305, nb090_alpha_dummy_306] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_386 (A : Class) : (nb090_alpha_dummy_305 A) ≠ (nb090_alpha_dummy_307 A) := by
  simpa only [nb090_alpha_dummy_305, nb090_alpha_dummy_307] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_387 (A : Class) : (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_307 A) := by
  simpa only [nb090_alpha_dummy_306, nb090_alpha_dummy_307] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_388 (u : Var) : (nb090_alpha_dummy_308 u) ∉ (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_308] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_389 (u : Var) : (nb090_alpha_dummy_309 u) ∉ (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_309] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_390 (u : Var) : (nb090_alpha_dummy_310 u) ∉ (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_310] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_391 (u : Var) : (nb090_alpha_dummy_308 u) ≠ (nb090_alpha_dummy_309 u) := by
  simpa only [nb090_alpha_dummy_308, nb090_alpha_dummy_309] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
