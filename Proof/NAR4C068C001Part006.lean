import NAR4C068C001Part005

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

theorem nb068_fresh_192 (f : Var) : (nb068_alpha_dummy_160 f) ∉ (((Class.cv (nb068_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) := by
  simpa only [nb068_alpha_dummy_160] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) 0

theorem nb068_fresh_193 : (nb068_alpha_dummy_175) ∉ (((Class.cv (nb068_alpha_dummy_168))).fv) := by
  simpa only [nb068_alpha_dummy_175] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_168))).fv) 0

theorem nb068_fresh_194 : (nb068_alpha_dummy_176) ∉ (((Class.cv (nb068_alpha_dummy_168))).fv) := by
  simpa only [nb068_alpha_dummy_176] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_168))).fv) 1

theorem nb068_distinct_195 : (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_176) := by
  simpa only [nb068_alpha_dummy_175, nb068_alpha_dummy_176] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_168))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_196 (f : Var) : (nb068_alpha_dummy_177 f) ∉ (((Class.cv (nb068_alpha_dummy_170 f))).fv) := by
  simpa only [nb068_alpha_dummy_177] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_170 f))).fv) 0

theorem nb068_fresh_197 (f : Var) : (nb068_alpha_dummy_178 f) ∉ (((Class.cv (nb068_alpha_dummy_170 f))).fv) := by
  simpa only [nb068_alpha_dummy_178] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_170 f))).fv) 1

theorem nb068_distinct_198 (f : Var) : (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_178 f) := by
  simpa only [nb068_alpha_dummy_177, nb068_alpha_dummy_178] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_170 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_199 : (nb068_alpha_dummy_181) ∉ (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_181] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_200 : (nb068_alpha_dummy_182) ∉ (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_182] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_201 : (nb068_alpha_dummy_183) ∉ (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_183] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_202 : (nb068_alpha_dummy_181) ≠ (nb068_alpha_dummy_182) := by
  simpa only [nb068_alpha_dummy_181, nb068_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_203 : (nb068_alpha_dummy_181) ≠ (nb068_alpha_dummy_183) := by
  simpa only [nb068_alpha_dummy_181, nb068_alpha_dummy_183] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_204 : (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_183) := by
  simpa only [nb068_alpha_dummy_182, nb068_alpha_dummy_183] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_205 (f : Var) : (nb068_alpha_dummy_184 f) ∉ (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_184] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_206 (f : Var) : (nb068_alpha_dummy_185 f) ∉ (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_185] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_207 (f : Var) : (nb068_alpha_dummy_186 f) ∉ (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_186] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_208 (f : Var) : (nb068_alpha_dummy_184 f) ≠ (nb068_alpha_dummy_185 f) := by
  simpa only [nb068_alpha_dummy_184, nb068_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_209 (f : Var) : (nb068_alpha_dummy_184 f) ≠ (nb068_alpha_dummy_186 f) := by
  simpa only [nb068_alpha_dummy_184, nb068_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_210 (f : Var) : (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_186 f) := by
  simpa only [nb068_alpha_dummy_185, nb068_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_211 : (nb068_alpha_dummy_193) ∉ (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_182))).fv) := by
  simpa only [nb068_alpha_dummy_193] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_182))).fv) 0

theorem nb068_fresh_212 : (nb068_alpha_dummy_189) ∉ (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) := by
  simpa only [nb068_alpha_dummy_189] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_182))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) 0

theorem nb068_fresh_213 : (nb068_alpha_dummy_195) ∉ (((Class.cv (nb068_alpha_dummy_183))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) := by
  simpa only [nb068_alpha_dummy_195] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_183))).fv ∪ ((Class.cv (nb068_alpha_dummy_183))).fv) 0

theorem nb068_fresh_214 (f : Var) : (nb068_alpha_dummy_194 f) ∉ (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_185 f))).fv) := by
  simpa only [nb068_alpha_dummy_194] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_185 f))).fv) 0

theorem nb068_fresh_215 (f : Var) : (nb068_alpha_dummy_190 f) ∉ (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) := by
  simpa only [nb068_alpha_dummy_190] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) 0

theorem nb068_fresh_216 (f : Var) : (nb068_alpha_dummy_196 f) ∉ (((Class.cv (nb068_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) := by
  simpa only [nb068_alpha_dummy_196] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_186 f))).fv) 0

theorem nb068_fresh_217 : (nb068_alpha_dummy_211) ∉ (((Class.cv (nb068_alpha_dummy_204))).fv) := by
  simpa only [nb068_alpha_dummy_211] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_204))).fv) 0

theorem nb068_fresh_218 : (nb068_alpha_dummy_212) ∉ (((Class.cv (nb068_alpha_dummy_204))).fv) := by
  simpa only [nb068_alpha_dummy_212] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_204))).fv) 1

theorem nb068_distinct_219 : (nb068_alpha_dummy_211) ≠ (nb068_alpha_dummy_212) := by
  simpa only [nb068_alpha_dummy_211, nb068_alpha_dummy_212] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_204))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_220 (f : Var) : (nb068_alpha_dummy_213 f) ∉ (((Class.cv (nb068_alpha_dummy_206 f))).fv) := by
  simpa only [nb068_alpha_dummy_213] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_206 f))).fv) 0

theorem nb068_fresh_221 (f : Var) : (nb068_alpha_dummy_214 f) ∉ (((Class.cv (nb068_alpha_dummy_206 f))).fv) := by
  simpa only [nb068_alpha_dummy_214] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_206 f))).fv) 1

theorem nb068_distinct_222 (f : Var) : (nb068_alpha_dummy_213 f) ≠ (nb068_alpha_dummy_214 f) := by
  simpa only [nb068_alpha_dummy_213, nb068_alpha_dummy_214] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_206 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_223 : (nb068_alpha_dummy_217) ∉ (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_217] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_224 : (nb068_alpha_dummy_218) ∉ (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_218] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_225 : (nb068_alpha_dummy_219) ∉ (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_219] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_226 : (nb068_alpha_dummy_217) ≠ (nb068_alpha_dummy_218) := by
  simpa only [nb068_alpha_dummy_217, nb068_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_227 : (nb068_alpha_dummy_217) ≠ (nb068_alpha_dummy_219) := by
  simpa only [nb068_alpha_dummy_217, nb068_alpha_dummy_219] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_228 : (nb068_alpha_dummy_218) ≠ (nb068_alpha_dummy_219) := by
  simpa only [nb068_alpha_dummy_218, nb068_alpha_dummy_219] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_229 (f : Var) : (nb068_alpha_dummy_220 f) ∉ (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_220] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_230 (f : Var) : (nb068_alpha_dummy_221 f) ∉ (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_221] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_231 (f : Var) : (nb068_alpha_dummy_222 f) ∉ (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_222] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_232 (f : Var) : (nb068_alpha_dummy_220 f) ≠ (nb068_alpha_dummy_221 f) := by
  simpa only [nb068_alpha_dummy_220, nb068_alpha_dummy_221] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_233 (f : Var) : (nb068_alpha_dummy_220 f) ≠ (nb068_alpha_dummy_222 f) := by
  simpa only [nb068_alpha_dummy_220, nb068_alpha_dummy_222] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_234 (f : Var) : (nb068_alpha_dummy_221 f) ≠ (nb068_alpha_dummy_222 f) := by
  simpa only [nb068_alpha_dummy_221, nb068_alpha_dummy_222] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_235 : (nb068_alpha_dummy_229) ∉ (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_218))).fv) := by
  simpa only [nb068_alpha_dummy_229] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_218))).fv) 0

theorem nb068_fresh_236 : (nb068_alpha_dummy_225) ∉ (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) := by
  simpa only [nb068_alpha_dummy_225] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) 0

theorem nb068_fresh_237 : (nb068_alpha_dummy_231) ∉ (((Class.cv (nb068_alpha_dummy_219))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) := by
  simpa only [nb068_alpha_dummy_231] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_219))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) 0

theorem nb068_fresh_238 (f : Var) : (nb068_alpha_dummy_230 f) ∉ (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_221 f))).fv) := by
  simpa only [nb068_alpha_dummy_230] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_221 f))).fv) 0

theorem nb068_fresh_239 (f : Var) : (nb068_alpha_dummy_226 f) ∉ (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) := by
  simpa only [nb068_alpha_dummy_226] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) 0

theorem nb068_fresh_240 (f : Var) : (nb068_alpha_dummy_232 f) ∉ (((Class.cv (nb068_alpha_dummy_222 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) := by
  simpa only [nb068_alpha_dummy_232] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_222 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) 0

theorem nb068_fresh_241 : (nb068_alpha_dummy_243) ∉ (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) := by
  simpa only [nb068_alpha_dummy_243] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) 0

theorem nb068_fresh_242 : (nb068_alpha_dummy_244) ∉ (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) := by
  simpa only [nb068_alpha_dummy_244] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) 1

theorem nb068_distinct_243 : (nb068_alpha_dummy_243) ≠ (nb068_alpha_dummy_244) := by
  simpa only [nb068_alpha_dummy_243, nb068_alpha_dummy_244] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_244 (f : Var) : (nb068_alpha_dummy_245 f) ∉ (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) := by
  simpa only [nb068_alpha_dummy_245] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) 0

theorem nb068_fresh_245 (f : Var) : (nb068_alpha_dummy_246 f) ∉ (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) := by
  simpa only [nb068_alpha_dummy_246] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) 1

theorem nb068_distinct_246 (f : Var) : (nb068_alpha_dummy_245 f) ≠ (nb068_alpha_dummy_246 f) := by
  simpa only [nb068_alpha_dummy_245, nb068_alpha_dummy_246] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_247 : (nb068_alpha_dummy_251) ∉ (((Class.cv (nb068_alpha_dummy_244))).fv) := by
  simpa only [nb068_alpha_dummy_251] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_244))).fv) 0

theorem nb068_fresh_248 : (nb068_alpha_dummy_252) ∉ (((Class.cv (nb068_alpha_dummy_244))).fv) := by
  simpa only [nb068_alpha_dummy_252] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_244))).fv) 1

theorem nb068_distinct_249 : (nb068_alpha_dummy_251) ≠ (nb068_alpha_dummy_252) := by
  simpa only [nb068_alpha_dummy_251, nb068_alpha_dummy_252] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_244))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_250 (f : Var) : (nb068_alpha_dummy_253 f) ∉ (((Class.cv (nb068_alpha_dummy_246 f))).fv) := by
  simpa only [nb068_alpha_dummy_253] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_246 f))).fv) 0

theorem nb068_fresh_251 (f : Var) : (nb068_alpha_dummy_254 f) ∉ (((Class.cv (nb068_alpha_dummy_246 f))).fv) := by
  simpa only [nb068_alpha_dummy_254] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_246 f))).fv) 1

theorem nb068_distinct_252 (f : Var) : (nb068_alpha_dummy_253 f) ≠ (nb068_alpha_dummy_254 f) := by
  simpa only [nb068_alpha_dummy_253, nb068_alpha_dummy_254] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_246 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_253 : (nb068_alpha_dummy_257) ∉ (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_257] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_254 : (nb068_alpha_dummy_258) ∉ (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_258] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_255 : (nb068_alpha_dummy_259) ∉ (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_259] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_256 : (nb068_alpha_dummy_257) ≠ (nb068_alpha_dummy_258) := by
  simpa only [nb068_alpha_dummy_257, nb068_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_257 : (nb068_alpha_dummy_257) ≠ (nb068_alpha_dummy_259) := by
  simpa only [nb068_alpha_dummy_257, nb068_alpha_dummy_259] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_258 : (nb068_alpha_dummy_258) ≠ (nb068_alpha_dummy_259) := by
  simpa only [nb068_alpha_dummy_258, nb068_alpha_dummy_259] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_259 (f : Var) : (nb068_alpha_dummy_260 f) ∉ (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_260] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_260 (f : Var) : (nb068_alpha_dummy_261 f) ∉ (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_261] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_261 (f : Var) : (nb068_alpha_dummy_262 f) ∉ (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_262] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_262 (f : Var) : (nb068_alpha_dummy_260 f) ≠ (nb068_alpha_dummy_261 f) := by
  simpa only [nb068_alpha_dummy_260, nb068_alpha_dummy_261] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_263 (f : Var) : (nb068_alpha_dummy_260 f) ≠ (nb068_alpha_dummy_262 f) := by
  simpa only [nb068_alpha_dummy_260, nb068_alpha_dummy_262] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_264 (f : Var) : (nb068_alpha_dummy_261 f) ≠ (nb068_alpha_dummy_262 f) := by
  simpa only [nb068_alpha_dummy_261, nb068_alpha_dummy_262] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_265 : (nb068_alpha_dummy_269) ∉ (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_258))).fv) := by
  simpa only [nb068_alpha_dummy_269] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_258))).fv) 0

theorem nb068_fresh_266 : (nb068_alpha_dummy_265) ∉ (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) := by
  simpa only [nb068_alpha_dummy_265] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) 0

theorem nb068_fresh_267 : (nb068_alpha_dummy_271) ∉ (((Class.cv (nb068_alpha_dummy_259))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) := by
  simpa only [nb068_alpha_dummy_271] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_259))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) 0

theorem nb068_fresh_268 (f : Var) : (nb068_alpha_dummy_270 f) ∉ (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_261 f))).fv) := by
  simpa only [nb068_alpha_dummy_270] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_261 f))).fv) 0

theorem nb068_fresh_269 (f : Var) : (nb068_alpha_dummy_266 f) ∉ (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) := by
  simpa only [nb068_alpha_dummy_266] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) 0

theorem nb068_fresh_270 (f : Var) : (nb068_alpha_dummy_272 f) ∉ (((Class.cv (nb068_alpha_dummy_262 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) := by
  simpa only [nb068_alpha_dummy_272] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_262 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) 0

theorem nb068_fresh_271 : (nb068_alpha_dummy_287) ∉ (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) := by
  simpa only [nb068_alpha_dummy_287] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) 0

theorem nb068_fresh_272 : (nb068_alpha_dummy_288) ∉ (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) := by
  simpa only [nb068_alpha_dummy_288] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) 1

theorem nb068_distinct_273 : (nb068_alpha_dummy_287) ≠ (nb068_alpha_dummy_288) := by
  simpa only [nb068_alpha_dummy_287, nb068_alpha_dummy_288] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_274 (f : Var) : (nb068_alpha_dummy_289 f) ∉ (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) := by
  simpa only [nb068_alpha_dummy_289] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) 0

theorem nb068_fresh_275 (f : Var) : (nb068_alpha_dummy_290 f) ∉ (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) := by
  simpa only [nb068_alpha_dummy_290] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) 1

theorem nb068_distinct_276 (f : Var) : (nb068_alpha_dummy_289 f) ≠ (nb068_alpha_dummy_290 f) := by
  simpa only [nb068_alpha_dummy_289, nb068_alpha_dummy_290] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_277 : (nb068_alpha_dummy_295) ∉ (((Class.cv (nb068_alpha_dummy_288))).fv) := by
  simpa only [nb068_alpha_dummy_295] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_288))).fv) 0

theorem nb068_fresh_278 : (nb068_alpha_dummy_296) ∉ (((Class.cv (nb068_alpha_dummy_288))).fv) := by
  simpa only [nb068_alpha_dummy_296] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_288))).fv) 1

theorem nb068_distinct_279 : (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_296) := by
  simpa only [nb068_alpha_dummy_295, nb068_alpha_dummy_296] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_288))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_280 (f : Var) : (nb068_alpha_dummy_297 f) ∉ (((Class.cv (nb068_alpha_dummy_290 f))).fv) := by
  simpa only [nb068_alpha_dummy_297] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_290 f))).fv) 0

theorem nb068_fresh_281 (f : Var) : (nb068_alpha_dummy_298 f) ∉ (((Class.cv (nb068_alpha_dummy_290 f))).fv) := by
  simpa only [nb068_alpha_dummy_298] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_290 f))).fv) 1

theorem nb068_distinct_282 (f : Var) : (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_298 f) := by
  simpa only [nb068_alpha_dummy_297, nb068_alpha_dummy_298] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_290 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_283 : (nb068_alpha_dummy_301) ∉ (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_301] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_284 : (nb068_alpha_dummy_302) ∉ (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_302] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_285 : (nb068_alpha_dummy_303) ∉ (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_303] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_286 : (nb068_alpha_dummy_301) ≠ (nb068_alpha_dummy_302) := by
  simpa only [nb068_alpha_dummy_301, nb068_alpha_dummy_302] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_287 : (nb068_alpha_dummy_301) ≠ (nb068_alpha_dummy_303) := by
  simpa only [nb068_alpha_dummy_301, nb068_alpha_dummy_303] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_288 : (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_303) := by
  simpa only [nb068_alpha_dummy_302, nb068_alpha_dummy_303] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_289 (f : Var) : (nb068_alpha_dummy_304 f) ∉ (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_304] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_290 (f : Var) : (nb068_alpha_dummy_305 f) ∉ (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_305] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_291 (f : Var) : (nb068_alpha_dummy_306 f) ∉ (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_306] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_292 (f : Var) : (nb068_alpha_dummy_304 f) ≠ (nb068_alpha_dummy_305 f) := by
  simpa only [nb068_alpha_dummy_304, nb068_alpha_dummy_305] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_293 (f : Var) : (nb068_alpha_dummy_304 f) ≠ (nb068_alpha_dummy_306 f) := by
  simpa only [nb068_alpha_dummy_304, nb068_alpha_dummy_306] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_294 (f : Var) : (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_306 f) := by
  simpa only [nb068_alpha_dummy_305, nb068_alpha_dummy_306] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_295 : (nb068_alpha_dummy_313) ∉ (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_302))).fv) := by
  simpa only [nb068_alpha_dummy_313] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_302))).fv) 0

theorem nb068_fresh_296 : (nb068_alpha_dummy_309) ∉ (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) := by
  simpa only [nb068_alpha_dummy_309] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) 0

theorem nb068_fresh_297 : (nb068_alpha_dummy_315) ∉ (((Class.cv (nb068_alpha_dummy_303))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) := by
  simpa only [nb068_alpha_dummy_315] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_303))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) 0

theorem nb068_fresh_298 (f : Var) : (nb068_alpha_dummy_314 f) ∉ (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_305 f))).fv) := by
  simpa only [nb068_alpha_dummy_314] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_305 f))).fv) 0

theorem nb068_fresh_299 (f : Var) : (nb068_alpha_dummy_310 f) ∉ (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) := by
  simpa only [nb068_alpha_dummy_310] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) 0

theorem nb068_fresh_300 (f : Var) : (nb068_alpha_dummy_316 f) ∉ (((Class.cv (nb068_alpha_dummy_306 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) := by
  simpa only [nb068_alpha_dummy_316] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_306 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) 0

theorem nb068_fresh_301 : (nb068_alpha_dummy_335) ∉ (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) := by
  simpa only [nb068_alpha_dummy_335] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) 0

theorem nb068_fresh_302 : (nb068_alpha_dummy_336) ∉ (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) := by
  simpa only [nb068_alpha_dummy_336] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) 1

theorem nb068_distinct_303 : (nb068_alpha_dummy_335) ≠ (nb068_alpha_dummy_336) := by
  simpa only [nb068_alpha_dummy_335, nb068_alpha_dummy_336] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_304 : (nb068_alpha_dummy_371) ∉ (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) := by
  simpa only [nb068_alpha_dummy_371] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) 0

theorem nb068_fresh_305 : (nb068_alpha_dummy_372) ∉ (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) := by
  simpa only [nb068_alpha_dummy_372] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) 1

theorem nb068_distinct_306 : (nb068_alpha_dummy_371) ≠ (nb068_alpha_dummy_372) := by
  simpa only [nb068_alpha_dummy_371, nb068_alpha_dummy_372] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_307 : (nb068_alpha_dummy_485) ∉ (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) := by
  simpa only [nb068_alpha_dummy_485] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) 0

theorem nb068_fresh_308 : (nb068_alpha_dummy_486) ∉ (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) := by
  simpa only [nb068_alpha_dummy_486] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) 1

theorem nb068_distinct_309 : (nb068_alpha_dummy_485) ≠ (nb068_alpha_dummy_486) := by
  simpa only [nb068_alpha_dummy_485, nb068_alpha_dummy_486] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_310 (f : Var) : (nb068_alpha_dummy_337 f) ∉ (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) := by
  simpa only [nb068_alpha_dummy_337] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) 0

theorem nb068_fresh_311 (f : Var) : (nb068_alpha_dummy_338 f) ∉ (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) := by
  simpa only [nb068_alpha_dummy_338] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) 1

theorem nb068_distinct_312 (f : Var) : (nb068_alpha_dummy_337 f) ≠ (nb068_alpha_dummy_338 f) := by
  simpa only [nb068_alpha_dummy_337, nb068_alpha_dummy_338] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_313 (f : Var) : (nb068_alpha_dummy_373 f) ∉ (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) := by
  simpa only [nb068_alpha_dummy_373] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) 0

theorem nb068_fresh_314 (f : Var) : (nb068_alpha_dummy_374 f) ∉ (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) := by
  simpa only [nb068_alpha_dummy_374] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) 1

theorem nb068_distinct_315 (f : Var) : (nb068_alpha_dummy_373 f) ≠ (nb068_alpha_dummy_374 f) := by
  simpa only [nb068_alpha_dummy_373, nb068_alpha_dummy_374] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_316 (f : Var) : (nb068_alpha_dummy_487 f) ∉ (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) := by
  simpa only [nb068_alpha_dummy_487] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) 0

theorem nb068_fresh_317 (f : Var) : (nb068_alpha_dummy_488 f) ∉ (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) := by
  simpa only [nb068_alpha_dummy_488] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) 1

theorem nb068_distinct_318 (f : Var) : (nb068_alpha_dummy_487 f) ≠ (nb068_alpha_dummy_488 f) := by
  simpa only [nb068_alpha_dummy_487, nb068_alpha_dummy_488] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_319 : (nb068_alpha_dummy_343) ∉ (((Class.cv (nb068_alpha_dummy_336))).fv) := by
  simpa only [nb068_alpha_dummy_343] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_336))).fv) 0

theorem nb068_fresh_320 : (nb068_alpha_dummy_344) ∉ (((Class.cv (nb068_alpha_dummy_336))).fv) := by
  simpa only [nb068_alpha_dummy_344] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_336))).fv) 1

theorem nb068_distinct_321 : (nb068_alpha_dummy_343) ≠ (nb068_alpha_dummy_344) := by
  simpa only [nb068_alpha_dummy_343, nb068_alpha_dummy_344] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_336))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_322 (f : Var) : (nb068_alpha_dummy_345 f) ∉ (((Class.cv (nb068_alpha_dummy_338 f))).fv) := by
  simpa only [nb068_alpha_dummy_345] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_338 f))).fv) 0

theorem nb068_fresh_323 (f : Var) : (nb068_alpha_dummy_346 f) ∉ (((Class.cv (nb068_alpha_dummy_338 f))).fv) := by
  simpa only [nb068_alpha_dummy_346] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_338 f))).fv) 1

theorem nb068_distinct_324 (f : Var) : (nb068_alpha_dummy_345 f) ≠ (nb068_alpha_dummy_346 f) := by
  simpa only [nb068_alpha_dummy_345, nb068_alpha_dummy_346] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_338 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_325 : (nb068_alpha_dummy_349) ∉ (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_349] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_326 : (nb068_alpha_dummy_350) ∉ (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_350] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_327 : (nb068_alpha_dummy_351) ∉ (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_351] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_328 : (nb068_alpha_dummy_349) ≠ (nb068_alpha_dummy_350) := by
  simpa only [nb068_alpha_dummy_349, nb068_alpha_dummy_350] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_329 : (nb068_alpha_dummy_349) ≠ (nb068_alpha_dummy_351) := by
  simpa only [nb068_alpha_dummy_349, nb068_alpha_dummy_351] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_330 : (nb068_alpha_dummy_350) ≠ (nb068_alpha_dummy_351) := by
  simpa only [nb068_alpha_dummy_350, nb068_alpha_dummy_351] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_331 (f : Var) : (nb068_alpha_dummy_352 f) ∉ (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_352] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_332 (f : Var) : (nb068_alpha_dummy_353 f) ∉ (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_353] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_333 (f : Var) : (nb068_alpha_dummy_354 f) ∉ (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_354] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_334 (f : Var) : (nb068_alpha_dummy_352 f) ≠ (nb068_alpha_dummy_353 f) := by
  simpa only [nb068_alpha_dummy_352, nb068_alpha_dummy_353] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_335 (f : Var) : (nb068_alpha_dummy_352 f) ≠ (nb068_alpha_dummy_354 f) := by
  simpa only [nb068_alpha_dummy_352, nb068_alpha_dummy_354] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_336 (f : Var) : (nb068_alpha_dummy_353 f) ≠ (nb068_alpha_dummy_354 f) := by
  simpa only [nb068_alpha_dummy_353, nb068_alpha_dummy_354] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_337 : (nb068_alpha_dummy_361) ∉ (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_350))).fv) := by
  simpa only [nb068_alpha_dummy_361] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_350))).fv) 0

theorem nb068_fresh_338 : (nb068_alpha_dummy_357) ∉ (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) := by
  simpa only [nb068_alpha_dummy_357] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_350))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) 0

theorem nb068_fresh_339 : (nb068_alpha_dummy_363) ∉ (((Class.cv (nb068_alpha_dummy_351))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) := by
  simpa only [nb068_alpha_dummy_363] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_351))).fv ∪ ((Class.cv (nb068_alpha_dummy_351))).fv) 0

theorem nb068_fresh_340 (f : Var) : (nb068_alpha_dummy_362 f) ∉ (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_353 f))).fv) := by
  simpa only [nb068_alpha_dummy_362] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_353 f))).fv) 0

theorem nb068_fresh_341 (f : Var) : (nb068_alpha_dummy_358 f) ∉ (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) := by
  simpa only [nb068_alpha_dummy_358] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_353 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_354 f))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
