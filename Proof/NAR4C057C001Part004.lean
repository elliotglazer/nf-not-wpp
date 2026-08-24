import NAR4C057C001Part003

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

theorem nb057_fresh_172 : (nb057_alpha_dummy_180) ∉ (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_180] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_173 : (nb057_alpha_dummy_181) ∉ (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_181] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_174 : (nb057_alpha_dummy_182) ∉ (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_182] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_175 : (nb057_alpha_dummy_180) ≠ (nb057_alpha_dummy_181) := by
  simpa only [nb057_alpha_dummy_180, nb057_alpha_dummy_181] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_176 : (nb057_alpha_dummy_180) ≠ (nb057_alpha_dummy_182) := by
  simpa only [nb057_alpha_dummy_180, nb057_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_177 : (nb057_alpha_dummy_181) ≠ (nb057_alpha_dummy_182) := by
  simpa only [nb057_alpha_dummy_181, nb057_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_178 (f : Var) : (nb057_alpha_dummy_183 f) ∉ (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_183] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_179 (f : Var) : (nb057_alpha_dummy_184 f) ∉ (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_184] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_180 (f : Var) : (nb057_alpha_dummy_185 f) ∉ (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_185] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_181 (f : Var) : (nb057_alpha_dummy_183 f) ≠ (nb057_alpha_dummy_184 f) := by
  simpa only [nb057_alpha_dummy_183, nb057_alpha_dummy_184] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_182 (f : Var) : (nb057_alpha_dummy_183 f) ≠ (nb057_alpha_dummy_185 f) := by
  simpa only [nb057_alpha_dummy_183, nb057_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_183 (f : Var) : (nb057_alpha_dummy_184 f) ≠ (nb057_alpha_dummy_185 f) := by
  simpa only [nb057_alpha_dummy_184, nb057_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_184 : (nb057_alpha_dummy_192) ∉ (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_181))).fv) := by
  simpa only [nb057_alpha_dummy_192] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_181))).fv) 0

theorem nb057_fresh_185 : (nb057_alpha_dummy_188) ∉ (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) := by
  simpa only [nb057_alpha_dummy_188] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) 0

theorem nb057_fresh_186 : (nb057_alpha_dummy_194) ∉ (((Class.cv (nb057_alpha_dummy_182))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) := by
  simpa only [nb057_alpha_dummy_194] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_182))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) 0

theorem nb057_fresh_187 (f : Var) : (nb057_alpha_dummy_193 f) ∉ (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_184 f))).fv) := by
  simpa only [nb057_alpha_dummy_193] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_184 f))).fv) 0

theorem nb057_fresh_188 (f : Var) : (nb057_alpha_dummy_189 f) ∉ (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) := by
  simpa only [nb057_alpha_dummy_189] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) 0

theorem nb057_fresh_189 (f : Var) : (nb057_alpha_dummy_195 f) ∉ (((Class.cv (nb057_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) := by
  simpa only [nb057_alpha_dummy_195] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) 0

theorem nb057_fresh_190 : (nb057_alpha_dummy_210) ∉ (((Class.cv (nb057_alpha_dummy_203))).fv) := by
  simpa only [nb057_alpha_dummy_210] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_203))).fv) 0

theorem nb057_fresh_191 : (nb057_alpha_dummy_211) ∉ (((Class.cv (nb057_alpha_dummy_203))).fv) := by
  simpa only [nb057_alpha_dummy_211] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_203))).fv) 1

theorem nb057_distinct_192 : (nb057_alpha_dummy_210) ≠ (nb057_alpha_dummy_211) := by
  simpa only [nb057_alpha_dummy_210, nb057_alpha_dummy_211] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_203))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_193 (f : Var) : (nb057_alpha_dummy_212 f) ∉ (((Class.cv (nb057_alpha_dummy_205 f))).fv) := by
  simpa only [nb057_alpha_dummy_212] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_205 f))).fv) 0

theorem nb057_fresh_194 (f : Var) : (nb057_alpha_dummy_213 f) ∉ (((Class.cv (nb057_alpha_dummy_205 f))).fv) := by
  simpa only [nb057_alpha_dummy_213] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_205 f))).fv) 1

theorem nb057_distinct_195 (f : Var) : (nb057_alpha_dummy_212 f) ≠ (nb057_alpha_dummy_213 f) := by
  simpa only [nb057_alpha_dummy_212, nb057_alpha_dummy_213] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_205 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_196 : (nb057_alpha_dummy_216) ∉ (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_216] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_197 : (nb057_alpha_dummy_217) ∉ (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_217] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_198 : (nb057_alpha_dummy_218) ∉ (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_218] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_199 : (nb057_alpha_dummy_216) ≠ (nb057_alpha_dummy_217) := by
  simpa only [nb057_alpha_dummy_216, nb057_alpha_dummy_217] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_200 : (nb057_alpha_dummy_216) ≠ (nb057_alpha_dummy_218) := by
  simpa only [nb057_alpha_dummy_216, nb057_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_201 : (nb057_alpha_dummy_217) ≠ (nb057_alpha_dummy_218) := by
  simpa only [nb057_alpha_dummy_217, nb057_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_202 (f : Var) : (nb057_alpha_dummy_219 f) ∉ (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_219] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_203 (f : Var) : (nb057_alpha_dummy_220 f) ∉ (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_220] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_204 (f : Var) : (nb057_alpha_dummy_221 f) ∉ (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_221] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_205 (f : Var) : (nb057_alpha_dummy_219 f) ≠ (nb057_alpha_dummy_220 f) := by
  simpa only [nb057_alpha_dummy_219, nb057_alpha_dummy_220] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_206 (f : Var) : (nb057_alpha_dummy_219 f) ≠ (nb057_alpha_dummy_221 f) := by
  simpa only [nb057_alpha_dummy_219, nb057_alpha_dummy_221] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_207 (f : Var) : (nb057_alpha_dummy_220 f) ≠ (nb057_alpha_dummy_221 f) := by
  simpa only [nb057_alpha_dummy_220, nb057_alpha_dummy_221] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_208 : (nb057_alpha_dummy_228) ∉ (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_217))).fv) := by
  simpa only [nb057_alpha_dummy_228] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_217))).fv) 0

theorem nb057_fresh_209 : (nb057_alpha_dummy_224) ∉ (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) := by
  simpa only [nb057_alpha_dummy_224] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) 0

theorem nb057_fresh_210 : (nb057_alpha_dummy_230) ∉ (((Class.cv (nb057_alpha_dummy_218))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) := by
  simpa only [nb057_alpha_dummy_230] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_218))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) 0

theorem nb057_fresh_211 (f : Var) : (nb057_alpha_dummy_229 f) ∉ (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_220 f))).fv) := by
  simpa only [nb057_alpha_dummy_229] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_220 f))).fv) 0

theorem nb057_fresh_212 (f : Var) : (nb057_alpha_dummy_225 f) ∉ (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) := by
  simpa only [nb057_alpha_dummy_225] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) 0

theorem nb057_fresh_213 (f : Var) : (nb057_alpha_dummy_231 f) ∉ (((Class.cv (nb057_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) := by
  simpa only [nb057_alpha_dummy_231] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) 0

theorem nb057_fresh_214 : (nb057_alpha_dummy_242) ∉ (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) := by
  simpa only [nb057_alpha_dummy_242] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) 0

theorem nb057_fresh_215 : (nb057_alpha_dummy_243) ∉ (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) := by
  simpa only [nb057_alpha_dummy_243] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) 1

theorem nb057_distinct_216 : (nb057_alpha_dummy_242) ≠ (nb057_alpha_dummy_243) := by
  simpa only [nb057_alpha_dummy_242, nb057_alpha_dummy_243] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_217 (f : Var) : (nb057_alpha_dummy_244 f) ∉ (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) := by
  simpa only [nb057_alpha_dummy_244] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) 0

theorem nb057_fresh_218 (f : Var) : (nb057_alpha_dummy_245 f) ∉ (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) := by
  simpa only [nb057_alpha_dummy_245] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) 1

theorem nb057_distinct_219 (f : Var) : (nb057_alpha_dummy_244 f) ≠ (nb057_alpha_dummy_245 f) := by
  simpa only [nb057_alpha_dummy_244, nb057_alpha_dummy_245] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_220 : (nb057_alpha_dummy_250) ∉ (((Class.cv (nb057_alpha_dummy_243))).fv) := by
  simpa only [nb057_alpha_dummy_250] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_243))).fv) 0

theorem nb057_fresh_221 : (nb057_alpha_dummy_251) ∉ (((Class.cv (nb057_alpha_dummy_243))).fv) := by
  simpa only [nb057_alpha_dummy_251] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_243))).fv) 1

theorem nb057_distinct_222 : (nb057_alpha_dummy_250) ≠ (nb057_alpha_dummy_251) := by
  simpa only [nb057_alpha_dummy_250, nb057_alpha_dummy_251] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_243))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_223 (f : Var) : (nb057_alpha_dummy_252 f) ∉ (((Class.cv (nb057_alpha_dummy_245 f))).fv) := by
  simpa only [nb057_alpha_dummy_252] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_245 f))).fv) 0

theorem nb057_fresh_224 (f : Var) : (nb057_alpha_dummy_253 f) ∉ (((Class.cv (nb057_alpha_dummy_245 f))).fv) := by
  simpa only [nb057_alpha_dummy_253] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_245 f))).fv) 1

theorem nb057_distinct_225 (f : Var) : (nb057_alpha_dummy_252 f) ≠ (nb057_alpha_dummy_253 f) := by
  simpa only [nb057_alpha_dummy_252, nb057_alpha_dummy_253] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_245 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_226 : (nb057_alpha_dummy_256) ∉ (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_256] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_227 : (nb057_alpha_dummy_257) ∉ (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_257] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_228 : (nb057_alpha_dummy_258) ∉ (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_258] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_229 : (nb057_alpha_dummy_256) ≠ (nb057_alpha_dummy_257) := by
  simpa only [nb057_alpha_dummy_256, nb057_alpha_dummy_257] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_230 : (nb057_alpha_dummy_256) ≠ (nb057_alpha_dummy_258) := by
  simpa only [nb057_alpha_dummy_256, nb057_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_231 : (nb057_alpha_dummy_257) ≠ (nb057_alpha_dummy_258) := by
  simpa only [nb057_alpha_dummy_257, nb057_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_232 (f : Var) : (nb057_alpha_dummy_259 f) ∉ (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_259] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_233 (f : Var) : (nb057_alpha_dummy_260 f) ∉ (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_260] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_234 (f : Var) : (nb057_alpha_dummy_261 f) ∉ (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_261] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_235 (f : Var) : (nb057_alpha_dummy_259 f) ≠ (nb057_alpha_dummy_260 f) := by
  simpa only [nb057_alpha_dummy_259, nb057_alpha_dummy_260] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_236 (f : Var) : (nb057_alpha_dummy_259 f) ≠ (nb057_alpha_dummy_261 f) := by
  simpa only [nb057_alpha_dummy_259, nb057_alpha_dummy_261] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_237 (f : Var) : (nb057_alpha_dummy_260 f) ≠ (nb057_alpha_dummy_261 f) := by
  simpa only [nb057_alpha_dummy_260, nb057_alpha_dummy_261] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_238 : (nb057_alpha_dummy_268) ∉ (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_257))).fv) := by
  simpa only [nb057_alpha_dummy_268] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_257))).fv) 0

theorem nb057_fresh_239 : (nb057_alpha_dummy_264) ∉ (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) := by
  simpa only [nb057_alpha_dummy_264] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) 0

theorem nb057_fresh_240 : (nb057_alpha_dummy_270) ∉ (((Class.cv (nb057_alpha_dummy_258))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) := by
  simpa only [nb057_alpha_dummy_270] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_258))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) 0

theorem nb057_fresh_241 (f : Var) : (nb057_alpha_dummy_269 f) ∉ (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_260 f))).fv) := by
  simpa only [nb057_alpha_dummy_269] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_260 f))).fv) 0

theorem nb057_fresh_242 (f : Var) : (nb057_alpha_dummy_265 f) ∉ (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) := by
  simpa only [nb057_alpha_dummy_265] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) 0

theorem nb057_fresh_243 (f : Var) : (nb057_alpha_dummy_271 f) ∉ (((Class.cv (nb057_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) := by
  simpa only [nb057_alpha_dummy_271] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) 0

theorem nb057_fresh_244 (f : Var) : (nb057_alpha_dummy_126 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb057_alpha_dummy_126] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb057_fresh_245 (f : Var) : (nb057_alpha_dummy_127 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb057_alpha_dummy_127] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb057_distinct_246 (f : Var) : (nb057_alpha_dummy_126 f) ≠ (nb057_alpha_dummy_127 f) := by
  simpa only [nb057_alpha_dummy_126, nb057_alpha_dummy_127] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_247 (f : Var) (a : Var) : (nb057_alpha_dummy_006 f a) ∉ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb057_alpha_dummy_006] using freshVar_not_mem (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 0

theorem nb057_fresh_248 (f : Var) (a : Var) : (nb057_alpha_dummy_007 f a) ∉ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb057_alpha_dummy_007] using freshVar_not_mem (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 1

theorem nb057_distinct_249 (f : Var) (a : Var) : (nb057_alpha_dummy_006 f a) ≠ (nb057_alpha_dummy_007 f a) := by
  simpa only [nb057_alpha_dummy_006, nb057_alpha_dummy_007] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_250 (f : Var) : (nb057_alpha_dummy_047 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb057_alpha_dummy_047] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb057_fresh_251 (f : Var) : (nb057_alpha_dummy_048 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb057_alpha_dummy_048] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb057_fresh_252 (f : Var) : (nb057_alpha_dummy_049 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb057_alpha_dummy_049] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb057_distinct_253 (f : Var) : (nb057_alpha_dummy_047 f) ≠ (nb057_alpha_dummy_048 f) := by
  simpa only [nb057_alpha_dummy_047, nb057_alpha_dummy_048] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_254 (f : Var) : (nb057_alpha_dummy_047 f) ≠ (nb057_alpha_dummy_049 f) := by
  simpa only [nb057_alpha_dummy_047, nb057_alpha_dummy_049] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_255 (f : Var) : (nb057_alpha_dummy_048 f) ≠ (nb057_alpha_dummy_049 f) := by
  simpa only [nb057_alpha_dummy_048, nb057_alpha_dummy_049] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_256 : (nb057_alpha_dummy_016) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_012)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_012)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_012))).fv) := by
  simpa only [nb057_alpha_dummy_016] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_012)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_012)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_012))).fv) 0

theorem nb057_fresh_257 (f : Var) (a : Var) : (nb057_alpha_dummy_017 f a) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_014 f a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_014 f a)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_014 f a))).fv) := by
  simpa only [nb057_alpha_dummy_017] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_014 f a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_014 f a)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_014 f a))).fv) 0

theorem nb057_fresh_258 : (nb057_alpha_dummy_064) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_060)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_060))).fv) := by
  simpa only [nb057_alpha_dummy_064] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_060)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_060))).fv) 0

theorem nb057_fresh_259 (f : Var) : (nb057_alpha_dummy_065 f) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_062 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_062 f))).fv) := by
  simpa only [nb057_alpha_dummy_065] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_062 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_062 f))).fv) 0

theorem nb057_fresh_260 : (nb057_alpha_dummy_100) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_096))).fv) := by
  simpa only [nb057_alpha_dummy_100] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_096))).fv) 0

theorem nb057_fresh_261 (f : Var) : (nb057_alpha_dummy_101 f) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_098 f))).fv) := by
  simpa only [nb057_alpha_dummy_101] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_098 f))).fv) 0

theorem nb057_fresh_262 : (nb057_alpha_dummy_142) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_138))).fv) := by
  simpa only [nb057_alpha_dummy_142] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_138))).fv) 0

theorem nb057_fresh_263 (f : Var) : (nb057_alpha_dummy_143 f) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_140 f))).fv) := by
  simpa only [nb057_alpha_dummy_143] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_140 f))).fv) 0

theorem nb057_fresh_264 : (nb057_alpha_dummy_178) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_174))).fv) := by
  simpa only [nb057_alpha_dummy_178] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_174))).fv) 0

theorem nb057_fresh_265 (f : Var) : (nb057_alpha_dummy_179 f) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_176 f))).fv) := by
  simpa only [nb057_alpha_dummy_179] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_176 f))).fv) 0

theorem nb057_fresh_266 : (nb057_alpha_dummy_214) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_210)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_210))).fv) := by
  simpa only [nb057_alpha_dummy_214] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_210)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_210))).fv) 0

theorem nb057_fresh_267 (f : Var) : (nb057_alpha_dummy_215 f) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_212 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_212 f))).fv) := by
  simpa only [nb057_alpha_dummy_215] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_212 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_212 f))).fv) 0

theorem nb057_fresh_268 : (nb057_alpha_dummy_254) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_250)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_250)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_250))).fv) := by
  simpa only [nb057_alpha_dummy_254] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_250)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_250)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_250))).fv) 0

theorem nb057_fresh_269 (f : Var) : (nb057_alpha_dummy_255 f) ∉ (((Wff.classMem (Class.cv (nb057_alpha_dummy_252 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_252 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_252 f))).fv) := by
  simpa only [nb057_alpha_dummy_255] using freshVar_not_mem (((Wff.classMem (Class.cv (nb057_alpha_dummy_252 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_252 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_252 f))).fv) 0

theorem nb057_fresh_270 : (nb057_alpha_dummy_238) ∉ (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb057_alpha_dummy_238] using freshVar_not_mem (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 0

theorem nb057_fresh_271 : (nb057_alpha_dummy_239) ∉ (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb057_alpha_dummy_239] using freshVar_not_mem (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 1

theorem nb057_distinct_272 : (nb057_alpha_dummy_238) ≠ (nb057_alpha_dummy_239) := by
  simpa only [nb057_alpha_dummy_238, nb057_alpha_dummy_239] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_273 (f : Var) : (nb057_alpha_dummy_240 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb057_alpha_dummy_240] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0

theorem nb057_fresh_274 (f : Var) : (nb057_alpha_dummy_241 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb057_alpha_dummy_241] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1

theorem nb057_distinct_275 (f : Var) : (nb057_alpha_dummy_240 f) ≠ (nb057_alpha_dummy_241 f) := by
  simpa only [nb057_alpha_dummy_240, nb057_alpha_dummy_241] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_276 : (nb057_alpha_dummy_042) ∉ (((syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb057_alpha_dummy_042] using freshVar_not_mem (((syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) 0

theorem nb057_fresh_277 (f : Var) : (nb057_alpha_dummy_043 f) ∉ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb057_alpha_dummy_043] using freshVar_not_mem (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb057_fresh_278 : (nb057_alpha_dummy_008) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_008] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_279 (f : Var) (a : Var) : (nb057_alpha_dummy_009 f a) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_009] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_280 : (nb057_alpha_dummy_056) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_056] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_281 (f : Var) : (nb057_alpha_dummy_057 f) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_057] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_282 : (nb057_alpha_dummy_092) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_092] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_283 (f : Var) : (nb057_alpha_dummy_093 f) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_093] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_284 : (nb057_alpha_dummy_134) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_134] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_285 (f : Var) : (nb057_alpha_dummy_135 f) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_135] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_286 : (nb057_alpha_dummy_170) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_170] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_287 (f : Var) : (nb057_alpha_dummy_171 f) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_171] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_288 : (nb057_alpha_dummy_206) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_206] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_289 (f : Var) : (nb057_alpha_dummy_207 f) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_207] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_290 : (nb057_alpha_dummy_246) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_246] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_291 (f : Var) : (nb057_alpha_dummy_247 f) ∉ (((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb057_alpha_dummy_247] using freshVar_not_mem (((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb057_fresh_292 : (nb057_alpha_dummy_028) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_019)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_020)))).fv) := by
  simpa only [nb057_alpha_dummy_028] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_019)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_020)))).fv) 0

theorem nb057_fresh_293 (f : Var) (a : Var) : (nb057_alpha_dummy_029 f a) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_022 f a)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_023 f a)))).fv) := by
  simpa only [nb057_alpha_dummy_029] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_022 f a)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_023 f a)))).fv) 0

theorem nb057_fresh_294 : (nb057_alpha_dummy_076) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_067)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_068)))).fv) := by
  simpa only [nb057_alpha_dummy_076] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_067)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_068)))).fv) 0

theorem nb057_fresh_295 (f : Var) : (nb057_alpha_dummy_077 f) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_070 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_071 f)))).fv) := by
  simpa only [nb057_alpha_dummy_077] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_070 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_071 f)))).fv) 0

theorem nb057_fresh_296 : (nb057_alpha_dummy_112) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_103)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_104)))).fv) := by
  simpa only [nb057_alpha_dummy_112] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_103)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_104)))).fv) 0

theorem nb057_fresh_297 (f : Var) : (nb057_alpha_dummy_113 f) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_106 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_107 f)))).fv) := by
  simpa only [nb057_alpha_dummy_113] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_106 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_107 f)))).fv) 0

theorem nb057_fresh_298 : (nb057_alpha_dummy_154) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_145)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_146)))).fv) := by
  simpa only [nb057_alpha_dummy_154] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_145)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_146)))).fv) 0

theorem nb057_fresh_299 (f : Var) : (nb057_alpha_dummy_155 f) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_148 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_149 f)))).fv) := by
  simpa only [nb057_alpha_dummy_155] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_148 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_149 f)))).fv) 0

theorem nb057_fresh_300 : (nb057_alpha_dummy_190) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_181)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_182)))).fv) := by
  simpa only [nb057_alpha_dummy_190] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_181)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_182)))).fv) 0

theorem nb057_fresh_301 (f : Var) : (nb057_alpha_dummy_191 f) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_184 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_185 f)))).fv) := by
  simpa only [nb057_alpha_dummy_191] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_184 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_185 f)))).fv) 0

theorem nb057_fresh_302 : (nb057_alpha_dummy_226) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_217)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_218)))).fv) := by
  simpa only [nb057_alpha_dummy_226] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_217)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_218)))).fv) 0

theorem nb057_fresh_303 (f : Var) : (nb057_alpha_dummy_227 f) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_220 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_221 f)))).fv) := by
  simpa only [nb057_alpha_dummy_227] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_220 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_221 f)))).fv) 0

theorem nb057_fresh_304 : (nb057_alpha_dummy_266) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_257)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_258)))).fv) := by
  simpa only [nb057_alpha_dummy_266] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_257)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_258)))).fv) 0

theorem nb057_fresh_305 (f : Var) : (nb057_alpha_dummy_267 f) ∉ (((syn_ccompl (Class.cv (nb057_alpha_dummy_260 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_261 f)))).fv) := by
  simpa only [nb057_alpha_dummy_267] using freshVar_not_mem (((syn_ccompl (Class.cv (nb057_alpha_dummy_260 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_261 f)))).fv) 0

theorem nb057_fresh_306 : (nb057_alpha_dummy_036) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_005))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_036] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_005))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_307 (f : Var) (a : Var) : (nb057_alpha_dummy_037 f a) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_037] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_308 : (nb057_alpha_dummy_084) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_053))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_084] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_053))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_309 (f : Var) : (nb057_alpha_dummy_085 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_085] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_310 : (nb057_alpha_dummy_120) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_089))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_120] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_089))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_311 (f : Var) : (nb057_alpha_dummy_121 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_121] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_312 : (nb057_alpha_dummy_162) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_131))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_162] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_131))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_313 (f : Var) : (nb057_alpha_dummy_163 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_163] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_314 : (nb057_alpha_dummy_198) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_167))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_198] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_167))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_315 (f : Var) : (nb057_alpha_dummy_199 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_199] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_316 : (nb057_alpha_dummy_234) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_203))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_234] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_203))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_317 (f : Var) : (nb057_alpha_dummy_235 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_235] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_318 : (nb057_alpha_dummy_274) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_243))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_274] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_243))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_319 (f : Var) : (nb057_alpha_dummy_275 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb057_alpha_dummy_275] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb057_fresh_320 : (nb057_alpha_dummy_024) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv) := by
  simpa only [nb057_alpha_dummy_024] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv) 0

theorem nb057_fresh_321 (f : Var) (a : Var) : (nb057_alpha_dummy_025 f a) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))).fv) := by
  simpa only [nb057_alpha_dummy_025] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
