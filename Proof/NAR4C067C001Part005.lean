import NAR4C067C001Part004

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

theorem nb067_fresh_221 : (nb067_alpha_dummy_233) ∉ (((Class.cv (nb067_alpha_dummy_221))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) := by
  simpa only [nb067_alpha_dummy_233] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_221))).fv ∪ ((Class.cv (nb067_alpha_dummy_221))).fv) 0

theorem nb067_fresh_222 (f : Var) : (nb067_alpha_dummy_232 f) ∉ (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_223 f))).fv) := by
  simpa only [nb067_alpha_dummy_232] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_223 f))).fv) 0

theorem nb067_fresh_223 (f : Var) : (nb067_alpha_dummy_228 f) ∉ (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) := by
  simpa only [nb067_alpha_dummy_228] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_223 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) 0

theorem nb067_fresh_224 (f : Var) : (nb067_alpha_dummy_234 f) ∉ (((Class.cv (nb067_alpha_dummy_224 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) := by
  simpa only [nb067_alpha_dummy_234] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_224 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_224 f))).fv) 0

theorem nb067_fresh_225 : (nb067_alpha_dummy_249) ∉ (((Class.cv (nb067_alpha_dummy_242))).fv) := by
  simpa only [nb067_alpha_dummy_249] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_242))).fv) 0

theorem nb067_fresh_226 : (nb067_alpha_dummy_250) ∉ (((Class.cv (nb067_alpha_dummy_242))).fv) := by
  simpa only [nb067_alpha_dummy_250] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_242))).fv) 1

theorem nb067_distinct_227 : (nb067_alpha_dummy_249) ≠ (nb067_alpha_dummy_250) := by
  simpa only [nb067_alpha_dummy_249, nb067_alpha_dummy_250] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_242))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_228 (f : Var) : (nb067_alpha_dummy_251 f) ∉ (((Class.cv (nb067_alpha_dummy_244 f))).fv) := by
  simpa only [nb067_alpha_dummy_251] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_244 f))).fv) 0

theorem nb067_fresh_229 (f : Var) : (nb067_alpha_dummy_252 f) ∉ (((Class.cv (nb067_alpha_dummy_244 f))).fv) := by
  simpa only [nb067_alpha_dummy_252] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_244 f))).fv) 1

theorem nb067_distinct_230 (f : Var) : (nb067_alpha_dummy_251 f) ≠ (nb067_alpha_dummy_252 f) := by
  simpa only [nb067_alpha_dummy_251, nb067_alpha_dummy_252] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_244 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_231 : (nb067_alpha_dummy_255) ∉ (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_255] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_232 : (nb067_alpha_dummy_256) ∉ (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_256] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_233 : (nb067_alpha_dummy_257) ∉ (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_257] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_234 : (nb067_alpha_dummy_255) ≠ (nb067_alpha_dummy_256) := by
  simpa only [nb067_alpha_dummy_255, nb067_alpha_dummy_256] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_235 : (nb067_alpha_dummy_255) ≠ (nb067_alpha_dummy_257) := by
  simpa only [nb067_alpha_dummy_255, nb067_alpha_dummy_257] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_236 : (nb067_alpha_dummy_256) ≠ (nb067_alpha_dummy_257) := by
  simpa only [nb067_alpha_dummy_256, nb067_alpha_dummy_257] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_237 (f : Var) : (nb067_alpha_dummy_258 f) ∉ (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_258] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_238 (f : Var) : (nb067_alpha_dummy_259 f) ∉ (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_259] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_239 (f : Var) : (nb067_alpha_dummy_260 f) ∉ (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_260] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_240 (f : Var) : (nb067_alpha_dummy_258 f) ≠ (nb067_alpha_dummy_259 f) := by
  simpa only [nb067_alpha_dummy_258, nb067_alpha_dummy_259] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_241 (f : Var) : (nb067_alpha_dummy_258 f) ≠ (nb067_alpha_dummy_260 f) := by
  simpa only [nb067_alpha_dummy_258, nb067_alpha_dummy_260] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_242 (f : Var) : (nb067_alpha_dummy_259 f) ≠ (nb067_alpha_dummy_260 f) := by
  simpa only [nb067_alpha_dummy_259, nb067_alpha_dummy_260] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_243 : (nb067_alpha_dummy_267) ∉ (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_256))).fv) := by
  simpa only [nb067_alpha_dummy_267] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_256))).fv) 0

theorem nb067_fresh_244 : (nb067_alpha_dummy_263) ∉ (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) := by
  simpa only [nb067_alpha_dummy_263] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_256))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) 0

theorem nb067_fresh_245 : (nb067_alpha_dummy_269) ∉ (((Class.cv (nb067_alpha_dummy_257))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) := by
  simpa only [nb067_alpha_dummy_269] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_257))).fv ∪ ((Class.cv (nb067_alpha_dummy_257))).fv) 0

theorem nb067_fresh_246 (f : Var) : (nb067_alpha_dummy_268 f) ∉ (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_259 f))).fv) := by
  simpa only [nb067_alpha_dummy_268] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_259 f))).fv) 0

theorem nb067_fresh_247 (f : Var) : (nb067_alpha_dummy_264 f) ∉ (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) := by
  simpa only [nb067_alpha_dummy_264] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_259 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) 0

theorem nb067_fresh_248 (f : Var) : (nb067_alpha_dummy_270 f) ∉ (((Class.cv (nb067_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) := by
  simpa only [nb067_alpha_dummy_270] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_260 f))).fv) 0

theorem nb067_fresh_249 : (nb067_alpha_dummy_281) ∉ (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) := by
  simpa only [nb067_alpha_dummy_281] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) 0

theorem nb067_fresh_250 : (nb067_alpha_dummy_282) ∉ (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) := by
  simpa only [nb067_alpha_dummy_282] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) 1

theorem nb067_distinct_251 : (nb067_alpha_dummy_281) ≠ (nb067_alpha_dummy_282) := by
  simpa only [nb067_alpha_dummy_281, nb067_alpha_dummy_282] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_252 (f : Var) : (nb067_alpha_dummy_283 f) ∉ (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) := by
  simpa only [nb067_alpha_dummy_283] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) 0

theorem nb067_fresh_253 (f : Var) : (nb067_alpha_dummy_284 f) ∉ (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) := by
  simpa only [nb067_alpha_dummy_284] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) 1

theorem nb067_distinct_254 (f : Var) : (nb067_alpha_dummy_283 f) ≠ (nb067_alpha_dummy_284 f) := by
  simpa only [nb067_alpha_dummy_283, nb067_alpha_dummy_284] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_255 : (nb067_alpha_dummy_289) ∉ (((Class.cv (nb067_alpha_dummy_282))).fv) := by
  simpa only [nb067_alpha_dummy_289] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_282))).fv) 0

theorem nb067_fresh_256 : (nb067_alpha_dummy_290) ∉ (((Class.cv (nb067_alpha_dummy_282))).fv) := by
  simpa only [nb067_alpha_dummy_290] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_282))).fv) 1

theorem nb067_distinct_257 : (nb067_alpha_dummy_289) ≠ (nb067_alpha_dummy_290) := by
  simpa only [nb067_alpha_dummy_289, nb067_alpha_dummy_290] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_282))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_258 (f : Var) : (nb067_alpha_dummy_291 f) ∉ (((Class.cv (nb067_alpha_dummy_284 f))).fv) := by
  simpa only [nb067_alpha_dummy_291] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_284 f))).fv) 0

theorem nb067_fresh_259 (f : Var) : (nb067_alpha_dummy_292 f) ∉ (((Class.cv (nb067_alpha_dummy_284 f))).fv) := by
  simpa only [nb067_alpha_dummy_292] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_284 f))).fv) 1

theorem nb067_distinct_260 (f : Var) : (nb067_alpha_dummy_291 f) ≠ (nb067_alpha_dummy_292 f) := by
  simpa only [nb067_alpha_dummy_291, nb067_alpha_dummy_292] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_284 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_261 : (nb067_alpha_dummy_295) ∉ (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_295] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_262 : (nb067_alpha_dummy_296) ∉ (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_296] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_263 : (nb067_alpha_dummy_297) ∉ (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_297] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_264 : (nb067_alpha_dummy_295) ≠ (nb067_alpha_dummy_296) := by
  simpa only [nb067_alpha_dummy_295, nb067_alpha_dummy_296] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_265 : (nb067_alpha_dummy_295) ≠ (nb067_alpha_dummy_297) := by
  simpa only [nb067_alpha_dummy_295, nb067_alpha_dummy_297] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_266 : (nb067_alpha_dummy_296) ≠ (nb067_alpha_dummy_297) := by
  simpa only [nb067_alpha_dummy_296, nb067_alpha_dummy_297] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_267 (f : Var) : (nb067_alpha_dummy_298 f) ∉ (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_298] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_268 (f : Var) : (nb067_alpha_dummy_299 f) ∉ (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_299] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_269 (f : Var) : (nb067_alpha_dummy_300 f) ∉ (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_300] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_270 (f : Var) : (nb067_alpha_dummy_298 f) ≠ (nb067_alpha_dummy_299 f) := by
  simpa only [nb067_alpha_dummy_298, nb067_alpha_dummy_299] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_271 (f : Var) : (nb067_alpha_dummy_298 f) ≠ (nb067_alpha_dummy_300 f) := by
  simpa only [nb067_alpha_dummy_298, nb067_alpha_dummy_300] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_272 (f : Var) : (nb067_alpha_dummy_299 f) ≠ (nb067_alpha_dummy_300 f) := by
  simpa only [nb067_alpha_dummy_299, nb067_alpha_dummy_300] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_273 : (nb067_alpha_dummy_307) ∉ (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_296))).fv) := by
  simpa only [nb067_alpha_dummy_307] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_296))).fv) 0

theorem nb067_fresh_274 : (nb067_alpha_dummy_303) ∉ (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) := by
  simpa only [nb067_alpha_dummy_303] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_296))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) 0

theorem nb067_fresh_275 : (nb067_alpha_dummy_309) ∉ (((Class.cv (nb067_alpha_dummy_297))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) := by
  simpa only [nb067_alpha_dummy_309] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_297))).fv ∪ ((Class.cv (nb067_alpha_dummy_297))).fv) 0

theorem nb067_fresh_276 (f : Var) : (nb067_alpha_dummy_308 f) ∉ (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_299 f))).fv) := by
  simpa only [nb067_alpha_dummy_308] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_299 f))).fv) 0

theorem nb067_fresh_277 (f : Var) : (nb067_alpha_dummy_304 f) ∉ (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) := by
  simpa only [nb067_alpha_dummy_304] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_299 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) 0

theorem nb067_fresh_278 (f : Var) : (nb067_alpha_dummy_310 f) ∉ (((Class.cv (nb067_alpha_dummy_300 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) := by
  simpa only [nb067_alpha_dummy_310] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_300 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_300 f))).fv) 0

theorem nb067_fresh_279 : (nb067_alpha_dummy_325) ∉ (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) := by
  simpa only [nb067_alpha_dummy_325] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) 0

theorem nb067_fresh_280 : (nb067_alpha_dummy_326) ∉ (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) := by
  simpa only [nb067_alpha_dummy_326] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) 1

theorem nb067_distinct_281 : (nb067_alpha_dummy_325) ≠ (nb067_alpha_dummy_326) := by
  simpa only [nb067_alpha_dummy_325, nb067_alpha_dummy_326] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_322))).fv ∪ ((Class.cv (nb067_alpha_dummy_321))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_282 (f : Var) : (nb067_alpha_dummy_327 f) ∉ (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) := by
  simpa only [nb067_alpha_dummy_327] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) 0

theorem nb067_fresh_283 (f : Var) : (nb067_alpha_dummy_328 f) ∉ (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) := by
  simpa only [nb067_alpha_dummy_328] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) 1

theorem nb067_distinct_284 (f : Var) : (nb067_alpha_dummy_327 f) ≠ (nb067_alpha_dummy_328 f) := by
  simpa only [nb067_alpha_dummy_327, nb067_alpha_dummy_328] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_324 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_323 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_285 : (nb067_alpha_dummy_333) ∉ (((Class.cv (nb067_alpha_dummy_326))).fv) := by
  simpa only [nb067_alpha_dummy_333] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_326))).fv) 0

theorem nb067_fresh_286 : (nb067_alpha_dummy_334) ∉ (((Class.cv (nb067_alpha_dummy_326))).fv) := by
  simpa only [nb067_alpha_dummy_334] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_326))).fv) 1

theorem nb067_distinct_287 : (nb067_alpha_dummy_333) ≠ (nb067_alpha_dummy_334) := by
  simpa only [nb067_alpha_dummy_333, nb067_alpha_dummy_334] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_326))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_288 (f : Var) : (nb067_alpha_dummy_335 f) ∉ (((Class.cv (nb067_alpha_dummy_328 f))).fv) := by
  simpa only [nb067_alpha_dummy_335] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_328 f))).fv) 0

theorem nb067_fresh_289 (f : Var) : (nb067_alpha_dummy_336 f) ∉ (((Class.cv (nb067_alpha_dummy_328 f))).fv) := by
  simpa only [nb067_alpha_dummy_336] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_328 f))).fv) 1

theorem nb067_distinct_290 (f : Var) : (nb067_alpha_dummy_335 f) ≠ (nb067_alpha_dummy_336 f) := by
  simpa only [nb067_alpha_dummy_335, nb067_alpha_dummy_336] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_328 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_291 : (nb067_alpha_dummy_339) ∉ (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_339] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_292 : (nb067_alpha_dummy_340) ∉ (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_340] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_293 : (nb067_alpha_dummy_341) ∉ (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_341] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_294 : (nb067_alpha_dummy_339) ≠ (nb067_alpha_dummy_340) := by
  simpa only [nb067_alpha_dummy_339, nb067_alpha_dummy_340] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_295 : (nb067_alpha_dummy_339) ≠ (nb067_alpha_dummy_341) := by
  simpa only [nb067_alpha_dummy_339, nb067_alpha_dummy_341] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_296 : (nb067_alpha_dummy_340) ≠ (nb067_alpha_dummy_341) := by
  simpa only [nb067_alpha_dummy_340, nb067_alpha_dummy_341] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_297 (f : Var) : (nb067_alpha_dummy_342 f) ∉ (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_342] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb067_fresh_298 (f : Var) : (nb067_alpha_dummy_343 f) ∉ (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_343] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb067_fresh_299 (f : Var) : (nb067_alpha_dummy_344 f) ∉ (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb067_alpha_dummy_344] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb067_distinct_300 (f : Var) : (nb067_alpha_dummy_342 f) ≠ (nb067_alpha_dummy_343 f) := by
  simpa only [nb067_alpha_dummy_342, nb067_alpha_dummy_343] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_301 (f : Var) : (nb067_alpha_dummy_342 f) ≠ (nb067_alpha_dummy_344 f) := by
  simpa only [nb067_alpha_dummy_342, nb067_alpha_dummy_344] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_302 (f : Var) : (nb067_alpha_dummy_343 f) ≠ (nb067_alpha_dummy_344 f) := by
  simpa only [nb067_alpha_dummy_343, nb067_alpha_dummy_344] using
    (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_303 : (nb067_alpha_dummy_351) ∉ (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_340))).fv) := by
  simpa only [nb067_alpha_dummy_351] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_340))).fv) 0

theorem nb067_fresh_304 : (nb067_alpha_dummy_347) ∉ (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) := by
  simpa only [nb067_alpha_dummy_347] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_340))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) 0

theorem nb067_fresh_305 : (nb067_alpha_dummy_353) ∉ (((Class.cv (nb067_alpha_dummy_341))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) := by
  simpa only [nb067_alpha_dummy_353] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_341))).fv ∪ ((Class.cv (nb067_alpha_dummy_341))).fv) 0

theorem nb067_fresh_306 (f : Var) : (nb067_alpha_dummy_352 f) ∉ (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_343 f))).fv) := by
  simpa only [nb067_alpha_dummy_352] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_343 f))).fv) 0

theorem nb067_fresh_307 (f : Var) : (nb067_alpha_dummy_348 f) ∉ (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) := by
  simpa only [nb067_alpha_dummy_348] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_343 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) 0

theorem nb067_fresh_308 (f : Var) : (nb067_alpha_dummy_354 f) ∉ (((Class.cv (nb067_alpha_dummy_344 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) := by
  simpa only [nb067_alpha_dummy_354] using freshVar_not_mem (((Class.cv (nb067_alpha_dummy_344 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_344 f))).fv) 0

theorem nb067_fresh_309 (f : Var) : (nb067_alpha_dummy_165 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb067_alpha_dummy_165] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb067_fresh_310 (f : Var) : (nb067_alpha_dummy_166 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb067_alpha_dummy_166] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb067_distinct_311 (f : Var) : (nb067_alpha_dummy_165 f) ≠ (nb067_alpha_dummy_166 f) := by
  simpa only [nb067_alpha_dummy_165, nb067_alpha_dummy_166] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_312 (f : Var) : (nb067_alpha_dummy_086 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb067_alpha_dummy_086] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb067_fresh_313 (f : Var) : (nb067_alpha_dummy_087 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb067_alpha_dummy_087] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb067_fresh_314 (f : Var) : (nb067_alpha_dummy_088 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb067_alpha_dummy_088] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb067_distinct_315 (f : Var) : (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_087 f) := by
  simpa only [nb067_alpha_dummy_086, nb067_alpha_dummy_087] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_316 (f : Var) : (nb067_alpha_dummy_086 f) ≠ (nb067_alpha_dummy_088 f) := by
  simpa only [nb067_alpha_dummy_086, nb067_alpha_dummy_088] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_317 (f : Var) : (nb067_alpha_dummy_087 f) ≠ (nb067_alpha_dummy_088 f) := by
  simpa only [nb067_alpha_dummy_087, nb067_alpha_dummy_088] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j := 2) (by decide))

theorem nb067_fresh_318 (f : Var) : (nb067_alpha_dummy_323 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_323] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 0

theorem nb067_fresh_319 (f : Var) : (nb067_alpha_dummy_324 f) ∉ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_324] using freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_cvv)).fv) 1

theorem nb067_distinct_320 (f : Var) : (nb067_alpha_dummy_323 f) ≠ (nb067_alpha_dummy_324 f) := by
  simpa only [nb067_alpha_dummy_323, nb067_alpha_dummy_324] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_321 (x : Var) (y : Var) : (nb067_alpha_dummy_017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb067_alpha_dummy_017] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb067_fresh_322 (x : Var) (y : Var) : (nb067_alpha_dummy_018 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb067_alpha_dummy_018] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb067_distinct_323 (x : Var) (y : Var) : (nb067_alpha_dummy_017 x y) ≠ (nb067_alpha_dummy_018 x y) := by
  simpa only [nb067_alpha_dummy_017, nb067_alpha_dummy_018] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_324 : (nb067_alpha_dummy_027) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_023)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_023)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_023))).fv) := by
  simpa only [nb067_alpha_dummy_027] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_023)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_023)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_023))).fv) 0

theorem nb067_fresh_325 (x : Var) (y : Var) : (nb067_alpha_dummy_028 x y) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_025 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_025 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_025 x y))).fv) := by
  simpa only [nb067_alpha_dummy_028] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_025 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_025 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_025 x y))).fv) 0

theorem nb067_fresh_326 : (nb067_alpha_dummy_055) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_051)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_051)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_051))).fv) := by
  simpa only [nb067_alpha_dummy_055] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_051)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_051)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_051))).fv) 0

theorem nb067_fresh_327 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_056 x y f) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_053 x y f))).fv) := by
  simpa only [nb067_alpha_dummy_056] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_053 x y f))).fv) 0

theorem nb067_fresh_328 : (nb067_alpha_dummy_103) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_099))).fv) := by
  simpa only [nb067_alpha_dummy_103] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_099))).fv) 0

theorem nb067_fresh_329 (f : Var) : (nb067_alpha_dummy_104 f) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_101 f))).fv) := by
  simpa only [nb067_alpha_dummy_104] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_101 f))).fv) 0

theorem nb067_fresh_330 : (nb067_alpha_dummy_139) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_135))).fv) := by
  simpa only [nb067_alpha_dummy_139] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_135))).fv) 0

theorem nb067_fresh_331 (f : Var) : (nb067_alpha_dummy_140 f) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_137 f))).fv) := by
  simpa only [nb067_alpha_dummy_140] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_137 f))).fv) 0

theorem nb067_fresh_332 : (nb067_alpha_dummy_181) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_177))).fv) := by
  simpa only [nb067_alpha_dummy_181] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_177))).fv) 0

theorem nb067_fresh_333 (f : Var) : (nb067_alpha_dummy_182 f) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_179 f))).fv) := by
  simpa only [nb067_alpha_dummy_182] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_179 f))).fv) 0

theorem nb067_fresh_334 : (nb067_alpha_dummy_217) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_213))).fv) := by
  simpa only [nb067_alpha_dummy_217] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_213))).fv) 0

theorem nb067_fresh_335 (f : Var) : (nb067_alpha_dummy_218 f) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_215 f))).fv) := by
  simpa only [nb067_alpha_dummy_218] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_215 f))).fv) 0

theorem nb067_fresh_336 : (nb067_alpha_dummy_253) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_249))).fv) := by
  simpa only [nb067_alpha_dummy_253] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_249))).fv) 0

theorem nb067_fresh_337 (f : Var) : (nb067_alpha_dummy_254 f) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_251 f))).fv) := by
  simpa only [nb067_alpha_dummy_254] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_251 f))).fv) 0

theorem nb067_fresh_338 : (nb067_alpha_dummy_293) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_289)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_289)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_289))).fv) := by
  simpa only [nb067_alpha_dummy_293] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_289)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_289)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_289))).fv) 0

theorem nb067_fresh_339 (f : Var) : (nb067_alpha_dummy_294 f) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_291 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_291 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_291 f))).fv) := by
  simpa only [nb067_alpha_dummy_294] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_291 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_291 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_291 f))).fv) 0

theorem nb067_fresh_340 : (nb067_alpha_dummy_337) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_333))).fv) := by
  simpa only [nb067_alpha_dummy_337] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_333))).fv) 0

theorem nb067_fresh_341 (f : Var) : (nb067_alpha_dummy_338 f) ∉ (((Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_335 f))).fv) := by
  simpa only [nb067_alpha_dummy_338] using freshVar_not_mem (((Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_335 f))).fv) 0

theorem nb067_fresh_342 : (nb067_alpha_dummy_277) ∉ (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_277] using freshVar_not_mem (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0

theorem nb067_fresh_343 : (nb067_alpha_dummy_278) ∉ (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_278] using freshVar_not_mem (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1

theorem nb067_distinct_344 : (nb067_alpha_dummy_277) ≠ (nb067_alpha_dummy_278) := by
  simpa only [nb067_alpha_dummy_277, nb067_alpha_dummy_278] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_345 (f : Var) : (nb067_alpha_dummy_279 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_279] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0

theorem nb067_fresh_346 (f : Var) : (nb067_alpha_dummy_280 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb067_alpha_dummy_280] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1

theorem nb067_distinct_347 (f : Var) : (nb067_alpha_dummy_279 f) ≠ (nb067_alpha_dummy_280 f) := by
  simpa only [nb067_alpha_dummy_279, nb067_alpha_dummy_280] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_348 : (nb067_alpha_dummy_081) ∉ (((syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb067_alpha_dummy_081] using freshVar_not_mem (((syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) 0

theorem nb067_fresh_349 (f : Var) : (nb067_alpha_dummy_082 f) ∉ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb067_alpha_dummy_082] using freshVar_not_mem (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb067_fresh_350 : (nb067_alpha_dummy_011) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_011] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_351 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_012 x y f) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_012] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_352 : (nb067_alpha_dummy_019) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_019] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_353 (x : Var) (y : Var) : (nb067_alpha_dummy_020 x y) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_020] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_354 : (nb067_alpha_dummy_095) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_095] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cphi (Class.cv (nb067_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_091) (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_091)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_355 (f : Var) : (nb067_alpha_dummy_096 f) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_096] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_093 f) (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_356 : (nb067_alpha_dummy_131) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_131] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_083)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cphi (Class.cv (nb067_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_127) (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_357 (f : Var) : (nb067_alpha_dummy_132 f) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_132] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_086 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_129 f) (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_358 : (nb067_alpha_dummy_173) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_173] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cphi (Class.cv (nb067_alpha_dummy_170)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_169) (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_169)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_359 (f : Var) : (nb067_alpha_dummy_174 f) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_174] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_171 f) (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_360 : (nb067_alpha_dummy_209) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_209] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_164)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cphi (Class.cv (nb067_alpha_dummy_206)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_205) (syn_wrex (nb067_alpha_dummy_206) (Class.cv (nb067_alpha_dummy_163)) (Wff.classEq (Class.cv (nb067_alpha_dummy_205)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_361 (f : Var) : (nb067_alpha_dummy_210 f) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_210] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_166 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_207 f) (syn_wrex (nb067_alpha_dummy_208 f) (Class.cv (nb067_alpha_dummy_165 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_362 : (nb067_alpha_dummy_245) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_245] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_085)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cphi (Class.cv (nb067_alpha_dummy_242)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_241) (syn_wrex (nb067_alpha_dummy_242) (Class.cv (nb067_alpha_dummy_084)) (Wff.classEq (Class.cv (nb067_alpha_dummy_241)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_242))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_363 (f : Var) : (nb067_alpha_dummy_246 f) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_246] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_243 f) (syn_wrex (nb067_alpha_dummy_244 f) (Class.cv (nb067_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_243 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_364 : (nb067_alpha_dummy_285) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_285] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_278)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_281) (syn_wrex (nb067_alpha_dummy_282) (Class.cv (nb067_alpha_dummy_277)) (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_282))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_365 (f : Var) : (nb067_alpha_dummy_286 f) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_286] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_280 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_283 f) (syn_wrex (nb067_alpha_dummy_284 f) (Class.cv (nb067_alpha_dummy_279 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_366 : (nb067_alpha_dummy_329) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_329] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_322)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cphi (Class.cv (nb067_alpha_dummy_326)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_325) (syn_wrex (nb067_alpha_dummy_326) (Class.cv (nb067_alpha_dummy_321)) (Wff.classEq (Class.cv (nb067_alpha_dummy_325)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_326))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_367 (f : Var) : (nb067_alpha_dummy_330 f) ∉ (((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb067_alpha_dummy_330] using freshVar_not_mem (((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_324 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_327 f) (syn_wrex (nb067_alpha_dummy_328 f) (Class.cv (nb067_alpha_dummy_323 f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_327 f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb067_fresh_368 : (nb067_alpha_dummy_039) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_030)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_031)))).fv) := by
  simpa only [nb067_alpha_dummy_039] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_030)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_031)))).fv) 0

theorem nb067_fresh_369 (x : Var) (y : Var) : (nb067_alpha_dummy_040 x y) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_033 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_034 x y)))).fv) := by
  simpa only [nb067_alpha_dummy_040] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_033 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_034 x y)))).fv) 0

theorem nb067_fresh_370 : (nb067_alpha_dummy_067) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_058)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_059)))).fv) := by
  simpa only [nb067_alpha_dummy_067] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_058)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_059)))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
