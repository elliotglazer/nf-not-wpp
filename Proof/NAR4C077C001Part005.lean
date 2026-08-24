import NAR4C077C001Part004

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

theorem nb077_distinct_219 (F : Class) (I : Class) : (nb077_alpha_dummy_233 F I) ≠ (nb077_alpha_dummy_235 F I) := by
  simpa only [nb077_alpha_dummy_233, nb077_alpha_dummy_235] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_220 (F : Class) (I : Class) : (nb077_alpha_dummy_234 F I) ≠ (nb077_alpha_dummy_235 F I) := by
  simpa only [nb077_alpha_dummy_234, nb077_alpha_dummy_235] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_227 F I))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_221 (x : Var) : (nb077_alpha_dummy_236 x) ∉ (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_236] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_222 (x : Var) : (nb077_alpha_dummy_237 x) ∉ (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_237] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_223 (x : Var) : (nb077_alpha_dummy_238 x) ∉ (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_238] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_224 (x : Var) : (nb077_alpha_dummy_236 x) ≠ (nb077_alpha_dummy_237 x) := by
  simpa only [nb077_alpha_dummy_236, nb077_alpha_dummy_237] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_225 (x : Var) : (nb077_alpha_dummy_236 x) ≠ (nb077_alpha_dummy_238 x) := by
  simpa only [nb077_alpha_dummy_236, nb077_alpha_dummy_238] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_226 (x : Var) : (nb077_alpha_dummy_237 x) ≠ (nb077_alpha_dummy_238 x) := by
  simpa only [nb077_alpha_dummy_237, nb077_alpha_dummy_238] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_229 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_227 (F : Class) (I : Class) : (nb077_alpha_dummy_245 F I) ∉ (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_234 F I))).fv) := by
  simpa only [nb077_alpha_dummy_245] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_234 F I))).fv) 0

theorem nb077_fresh_228 (F : Class) (I : Class) : (nb077_alpha_dummy_241 F I) ∉ (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_235 F I))).fv) := by
  simpa only [nb077_alpha_dummy_241] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_234 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_235 F I))).fv) 0

theorem nb077_fresh_229 (F : Class) (I : Class) : (nb077_alpha_dummy_247 F I) ∉ (((Class.cv (nb077_alpha_dummy_235 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_235 F I))).fv) := by
  simpa only [nb077_alpha_dummy_247] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_235 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_235 F I))).fv) 0

theorem nb077_fresh_230 (x : Var) : (nb077_alpha_dummy_246 x) ∉ (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_237 x))).fv) := by
  simpa only [nb077_alpha_dummy_246] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_237 x))).fv) 0

theorem nb077_fresh_231 (x : Var) : (nb077_alpha_dummy_242 x) ∉ (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) := by
  simpa only [nb077_alpha_dummy_242] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_237 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) 0

theorem nb077_fresh_232 (x : Var) : (nb077_alpha_dummy_248 x) ∉ (((Class.cv (nb077_alpha_dummy_238 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) := by
  simpa only [nb077_alpha_dummy_248] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_238 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_238 x))).fv) 0

theorem nb077_fresh_233 (F : Class) (I : Class) : (nb077_alpha_dummy_267 F I) ∉ (((Class.cv (nb077_alpha_dummy_260 F I))).fv) := by
  simpa only [nb077_alpha_dummy_267] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_260 F I))).fv) 0

theorem nb077_fresh_234 (F : Class) (I : Class) : (nb077_alpha_dummy_268 F I) ∉ (((Class.cv (nb077_alpha_dummy_260 F I))).fv) := by
  simpa only [nb077_alpha_dummy_268] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_260 F I))).fv) 1

theorem nb077_distinct_235 (F : Class) (I : Class) : (nb077_alpha_dummy_267 F I) ≠ (nb077_alpha_dummy_268 F I) := by
  simpa only [nb077_alpha_dummy_267, nb077_alpha_dummy_268] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_260 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_236 (x : Var) : (nb077_alpha_dummy_269 x) ∉ (((Class.cv (nb077_alpha_dummy_262 x))).fv) := by
  simpa only [nb077_alpha_dummy_269] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_262 x))).fv) 0

theorem nb077_fresh_237 (x : Var) : (nb077_alpha_dummy_270 x) ∉ (((Class.cv (nb077_alpha_dummy_262 x))).fv) := by
  simpa only [nb077_alpha_dummy_270] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_262 x))).fv) 1

theorem nb077_distinct_238 (x : Var) : (nb077_alpha_dummy_269 x) ≠ (nb077_alpha_dummy_270 x) := by
  simpa only [nb077_alpha_dummy_269, nb077_alpha_dummy_270] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_262 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_239 (F : Class) (I : Class) : (nb077_alpha_dummy_273 F I) ∉ (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_273] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_240 (F : Class) (I : Class) : (nb077_alpha_dummy_274 F I) ∉ (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_274] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_241 (F : Class) (I : Class) : (nb077_alpha_dummy_275 F I) ∉ (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_275] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_242 (F : Class) (I : Class) : (nb077_alpha_dummy_273 F I) ≠ (nb077_alpha_dummy_274 F I) := by
  simpa only [nb077_alpha_dummy_273, nb077_alpha_dummy_274] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_243 (F : Class) (I : Class) : (nb077_alpha_dummy_273 F I) ≠ (nb077_alpha_dummy_275 F I) := by
  simpa only [nb077_alpha_dummy_273, nb077_alpha_dummy_275] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_244 (F : Class) (I : Class) : (nb077_alpha_dummy_274 F I) ≠ (nb077_alpha_dummy_275 F I) := by
  simpa only [nb077_alpha_dummy_274, nb077_alpha_dummy_275] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_267 F I))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_245 (x : Var) : (nb077_alpha_dummy_276 x) ∉ (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_276] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_246 (x : Var) : (nb077_alpha_dummy_277 x) ∉ (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_277] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_247 (x : Var) : (nb077_alpha_dummy_278 x) ∉ (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_278] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_248 (x : Var) : (nb077_alpha_dummy_276 x) ≠ (nb077_alpha_dummy_277 x) := by
  simpa only [nb077_alpha_dummy_276, nb077_alpha_dummy_277] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_249 (x : Var) : (nb077_alpha_dummy_276 x) ≠ (nb077_alpha_dummy_278 x) := by
  simpa only [nb077_alpha_dummy_276, nb077_alpha_dummy_278] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_250 (x : Var) : (nb077_alpha_dummy_277 x) ≠ (nb077_alpha_dummy_278 x) := by
  simpa only [nb077_alpha_dummy_277, nb077_alpha_dummy_278] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_269 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_251 (F : Class) (I : Class) : (nb077_alpha_dummy_285 F I) ∉ (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_274 F I))).fv) := by
  simpa only [nb077_alpha_dummy_285] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_274 F I))).fv) 0

theorem nb077_fresh_252 (F : Class) (I : Class) : (nb077_alpha_dummy_281 F I) ∉ (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_275 F I))).fv) := by
  simpa only [nb077_alpha_dummy_281] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_274 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_275 F I))).fv) 0

theorem nb077_fresh_253 (F : Class) (I : Class) : (nb077_alpha_dummy_287 F I) ∉ (((Class.cv (nb077_alpha_dummy_275 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_275 F I))).fv) := by
  simpa only [nb077_alpha_dummy_287] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_275 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_275 F I))).fv) 0

theorem nb077_fresh_254 (x : Var) : (nb077_alpha_dummy_286 x) ∉ (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_277 x))).fv) := by
  simpa only [nb077_alpha_dummy_286] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_277 x))).fv) 0

theorem nb077_fresh_255 (x : Var) : (nb077_alpha_dummy_282 x) ∉ (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) := by
  simpa only [nb077_alpha_dummy_282] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_277 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) 0

theorem nb077_fresh_256 (x : Var) : (nb077_alpha_dummy_288 x) ∉ (((Class.cv (nb077_alpha_dummy_278 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) := by
  simpa only [nb077_alpha_dummy_288] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_278 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_278 x))).fv) 0

theorem nb077_fresh_257 (F : Class) (I : Class) : (nb077_alpha_dummy_307 F I) ∉ (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_296 F I))).fv) := by
  simpa only [nb077_alpha_dummy_307] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_296 F I))).fv) 0

theorem nb077_fresh_258 (F : Class) (I : Class) : (nb077_alpha_dummy_303 F I) ∉ (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_297 F I))).fv) := by
  simpa only [nb077_alpha_dummy_303] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_297 F I))).fv) 0

theorem nb077_fresh_259 (F : Class) (I : Class) : (nb077_alpha_dummy_309 F I) ∉ (((Class.cv (nb077_alpha_dummy_297 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_297 F I))).fv) := by
  simpa only [nb077_alpha_dummy_309] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_297 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_297 F I))).fv) 0

theorem nb077_fresh_260 (x : Var) : (nb077_alpha_dummy_308 x) ∉ (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_299 x))).fv) := by
  simpa only [nb077_alpha_dummy_308] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_299 x))).fv) 0

theorem nb077_fresh_261 (x : Var) : (nb077_alpha_dummy_304 x) ∉ (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) := by
  simpa only [nb077_alpha_dummy_304] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) 0

theorem nb077_fresh_262 (x : Var) : (nb077_alpha_dummy_310 x) ∉ (((Class.cv (nb077_alpha_dummy_300 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) := by
  simpa only [nb077_alpha_dummy_310] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_300 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) 0

theorem nb077_fresh_263 (F : Class) (I : Class) : (nb077_alpha_dummy_319 F I) ∉ (((Class.cv (nb077_alpha_dummy_312 F I))).fv) := by
  simpa only [nb077_alpha_dummy_319] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_312 F I))).fv) 0

theorem nb077_fresh_264 (F : Class) (I : Class) : (nb077_alpha_dummy_320 F I) ∉ (((Class.cv (nb077_alpha_dummy_312 F I))).fv) := by
  simpa only [nb077_alpha_dummy_320] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_312 F I))).fv) 1

theorem nb077_distinct_265 (F : Class) (I : Class) : (nb077_alpha_dummy_319 F I) ≠ (nb077_alpha_dummy_320 F I) := by
  simpa only [nb077_alpha_dummy_319, nb077_alpha_dummy_320] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_312 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_266 (x : Var) : (nb077_alpha_dummy_321 x) ∉ (((Class.cv (nb077_alpha_dummy_314 x))).fv) := by
  simpa only [nb077_alpha_dummy_321] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_314 x))).fv) 0

theorem nb077_fresh_267 (x : Var) : (nb077_alpha_dummy_322 x) ∉ (((Class.cv (nb077_alpha_dummy_314 x))).fv) := by
  simpa only [nb077_alpha_dummy_322] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_314 x))).fv) 1

theorem nb077_distinct_268 (x : Var) : (nb077_alpha_dummy_321 x) ≠ (nb077_alpha_dummy_322 x) := by
  simpa only [nb077_alpha_dummy_321, nb077_alpha_dummy_322] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_314 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_269 (F : Class) (I : Class) : (nb077_alpha_dummy_325 F I) ∉ (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_325] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_270 (F : Class) (I : Class) : (nb077_alpha_dummy_326 F I) ∉ (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_326] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_271 (F : Class) (I : Class) : (nb077_alpha_dummy_327 F I) ∉ (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_327] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_272 (F : Class) (I : Class) : (nb077_alpha_dummy_325 F I) ≠ (nb077_alpha_dummy_326 F I) := by
  simpa only [nb077_alpha_dummy_325, nb077_alpha_dummy_326] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_273 (F : Class) (I : Class) : (nb077_alpha_dummy_325 F I) ≠ (nb077_alpha_dummy_327 F I) := by
  simpa only [nb077_alpha_dummy_325, nb077_alpha_dummy_327] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_274 (F : Class) (I : Class) : (nb077_alpha_dummy_326 F I) ≠ (nb077_alpha_dummy_327 F I) := by
  simpa only [nb077_alpha_dummy_326, nb077_alpha_dummy_327] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_275 (x : Var) : (nb077_alpha_dummy_328 x) ∉ (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_328] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_276 (x : Var) : (nb077_alpha_dummy_329 x) ∉ (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_329] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_277 (x : Var) : (nb077_alpha_dummy_330 x) ∉ (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_330] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_278 (x : Var) : (nb077_alpha_dummy_328 x) ≠ (nb077_alpha_dummy_329 x) := by
  simpa only [nb077_alpha_dummy_328, nb077_alpha_dummy_329] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_279 (x : Var) : (nb077_alpha_dummy_328 x) ≠ (nb077_alpha_dummy_330 x) := by
  simpa only [nb077_alpha_dummy_328, nb077_alpha_dummy_330] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_280 (x : Var) : (nb077_alpha_dummy_329 x) ≠ (nb077_alpha_dummy_330 x) := by
  simpa only [nb077_alpha_dummy_329, nb077_alpha_dummy_330] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_281 (F : Class) (I : Class) : (nb077_alpha_dummy_337 F I) ∉ (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_326 F I))).fv) := by
  simpa only [nb077_alpha_dummy_337] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_326 F I))).fv) 0

theorem nb077_fresh_282 (F : Class) (I : Class) : (nb077_alpha_dummy_333 F I) ∉ (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_327 F I))).fv) := by
  simpa only [nb077_alpha_dummy_333] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_327 F I))).fv) 0

theorem nb077_fresh_283 (F : Class) (I : Class) : (nb077_alpha_dummy_339 F I) ∉ (((Class.cv (nb077_alpha_dummy_327 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_327 F I))).fv) := by
  simpa only [nb077_alpha_dummy_339] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_327 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_327 F I))).fv) 0

theorem nb077_fresh_284 (x : Var) : (nb077_alpha_dummy_338 x) ∉ (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_329 x))).fv) := by
  simpa only [nb077_alpha_dummy_338] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_329 x))).fv) 0

theorem nb077_fresh_285 (x : Var) : (nb077_alpha_dummy_334 x) ∉ (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) := by
  simpa only [nb077_alpha_dummy_334] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) 0

theorem nb077_fresh_286 (x : Var) : (nb077_alpha_dummy_340 x) ∉ (((Class.cv (nb077_alpha_dummy_330 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) := by
  simpa only [nb077_alpha_dummy_340] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_330 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) 0

theorem nb077_fresh_287 (x : Var) : (nb077_alpha_dummy_261 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) := by
  simpa only [nb077_alpha_dummy_261] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) 0

theorem nb077_fresh_288 (x : Var) : (nb077_alpha_dummy_262 x) ∉ (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) := by
  simpa only [nb077_alpha_dummy_262] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) 1

theorem nb077_distinct_289 (x : Var) : (nb077_alpha_dummy_261 x) ≠ (nb077_alpha_dummy_262 x) := by
  simpa only [nb077_alpha_dummy_261, nb077_alpha_dummy_262] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb077_alpha_dummy_256 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_290 (x : Var) : (nb077_alpha_dummy_298 x) ∉ (((Class.cv x)).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_298] using freshVar_not_mem (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_291 (x : Var) : (nb077_alpha_dummy_299 x) ∉ (((Class.cv x)).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_299] using freshVar_not_mem (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_292 (x : Var) : (nb077_alpha_dummy_300 x) ∉ (((Class.cv x)).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_300] using freshVar_not_mem (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_293 (x : Var) : (nb077_alpha_dummy_298 x) ≠ (nb077_alpha_dummy_299 x) := by
  simpa only [nb077_alpha_dummy_298, nb077_alpha_dummy_299] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_294 (x : Var) : (nb077_alpha_dummy_298 x) ≠ (nb077_alpha_dummy_300 x) := by
  simpa only [nb077_alpha_dummy_298, nb077_alpha_dummy_300] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_295 (x : Var) : (nb077_alpha_dummy_299 x) ≠ (nb077_alpha_dummy_300 x) := by
  simpa only [nb077_alpha_dummy_299, nb077_alpha_dummy_300] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_296 (F : Class) (I : Class) : (nb077_alpha_dummy_031 F I) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_027 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_027 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_027 F I))).fv) := by
  simpa only [nb077_alpha_dummy_031] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_027 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_027 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_027 F I))).fv) 0

theorem nb077_fresh_297 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_032 x F I) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_029 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_032] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_029 x F I))).fv) 0

theorem nb077_fresh_298 (F : Class) (I : Class) : (nb077_alpha_dummy_079 F I) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_075 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_075 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_075 F I))).fv) := by
  simpa only [nb077_alpha_dummy_079] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_075 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_075 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_075 F I))).fv) 0

theorem nb077_fresh_299 (x : Var) : (nb077_alpha_dummy_080 x) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_077 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_077 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_077 x))).fv) := by
  simpa only [nb077_alpha_dummy_080] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_077 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_077 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_077 x))).fv) 0

theorem nb077_fresh_300 (F : Class) (I : Class) : (nb077_alpha_dummy_115 F I) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_111 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_111 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_111 F I))).fv) := by
  simpa only [nb077_alpha_dummy_115] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_111 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_111 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_111 F I))).fv) 0

theorem nb077_fresh_301 (x : Var) : (nb077_alpha_dummy_116 x) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_113 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_113 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_113 x))).fv) := by
  simpa only [nb077_alpha_dummy_116] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_113 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_113 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_113 x))).fv) 0

theorem nb077_fresh_302 (F : Class) (I : Class) : (nb077_alpha_dummy_159 F I) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_155 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_155 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_155 F I))).fv) := by
  simpa only [nb077_alpha_dummy_159] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_155 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_155 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_155 F I))).fv) 0

theorem nb077_fresh_303 (x : Var) : (nb077_alpha_dummy_160 x) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_157 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_157 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_157 x))).fv) := by
  simpa only [nb077_alpha_dummy_160] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_157 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_157 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_157 x))).fv) 0

theorem nb077_fresh_304 (F : Class) (I : Class) : (nb077_alpha_dummy_195 F I) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_191 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_191 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_191 F I))).fv) := by
  simpa only [nb077_alpha_dummy_195] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_191 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_191 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_191 F I))).fv) 0

theorem nb077_fresh_305 (x : Var) : (nb077_alpha_dummy_196 x) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_193 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_193 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_193 x))).fv) := by
  simpa only [nb077_alpha_dummy_196] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_193 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_193 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_193 x))).fv) 0

theorem nb077_fresh_306 (F : Class) (I : Class) : (nb077_alpha_dummy_231 F I) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_227 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_227 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_227 F I))).fv) := by
  simpa only [nb077_alpha_dummy_231] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_227 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_227 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_227 F I))).fv) 0

theorem nb077_fresh_307 (x : Var) : (nb077_alpha_dummy_232 x) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_229 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_229 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_229 x))).fv) := by
  simpa only [nb077_alpha_dummy_232] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_229 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_229 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_229 x))).fv) 0

theorem nb077_fresh_308 (F : Class) (I : Class) : (nb077_alpha_dummy_271 F I) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_267 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_267 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_267 F I))).fv) := by
  simpa only [nb077_alpha_dummy_271] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_267 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_267 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_267 F I))).fv) 0

theorem nb077_fresh_309 (x : Var) : (nb077_alpha_dummy_272 x) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_269 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_269 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_269 x))).fv) := by
  simpa only [nb077_alpha_dummy_272] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_269 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_269 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_269 x))).fv) 0

theorem nb077_fresh_310 (F : Class) (I : Class) : (nb077_alpha_dummy_323 F I) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_319 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_319 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_319 F I))).fv) := by
  simpa only [nb077_alpha_dummy_323] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_319 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_319 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_319 F I))).fv) 0

theorem nb077_fresh_311 (x : Var) : (nb077_alpha_dummy_324 x) ∉ (((Wff.classMem (Class.cv (nb077_alpha_dummy_321 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_321 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_321 x))).fv) := by
  simpa only [nb077_alpha_dummy_324] using freshVar_not_mem (((Wff.classMem (Class.cv (nb077_alpha_dummy_321 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_321 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_321 x))).fv) 0

theorem nb077_fresh_312 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ∉ (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) := by
  simpa only [nb077_alpha_dummy_059] using freshVar_not_mem (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) 0

theorem nb077_fresh_313 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∉ (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) := by
  simpa only [nb077_alpha_dummy_060] using freshVar_not_mem (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) 1

theorem nb077_fresh_314 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∉ (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) := by
  simpa only [nb077_alpha_dummy_061] using freshVar_not_mem (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) 2

theorem nb077_distinct_315 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_060 F I) := by
  simpa only [nb077_alpha_dummy_059, nb077_alpha_dummy_060] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_316 (F : Class) (I : Class) : (nb077_alpha_dummy_059 F I) ≠ (nb077_alpha_dummy_061 F I) := by
  simpa only [nb077_alpha_dummy_059, nb077_alpha_dummy_061] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_317 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ≠ (nb077_alpha_dummy_061 F I) := by
  simpa only [nb077_alpha_dummy_060, nb077_alpha_dummy_061] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_318 (x : Var) : (nb077_alpha_dummy_062 x) ∉ (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) := by
  simpa only [nb077_alpha_dummy_062] using freshVar_not_mem (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) 0

theorem nb077_fresh_319 (x : Var) : (nb077_alpha_dummy_063 x) ∉ (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) := by
  simpa only [nb077_alpha_dummy_063] using freshVar_not_mem (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) 1

theorem nb077_fresh_320 (x : Var) : (nb077_alpha_dummy_064 x) ∉ (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) := by
  simpa only [nb077_alpha_dummy_064] using freshVar_not_mem (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) 2

theorem nb077_distinct_321 (x : Var) : (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_063 x) := by
  simpa only [nb077_alpha_dummy_062, nb077_alpha_dummy_063] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_322 (x : Var) : (nb077_alpha_dummy_062 x) ≠ (nb077_alpha_dummy_064 x) := by
  simpa only [nb077_alpha_dummy_062, nb077_alpha_dummy_064] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_323 (x : Var) : (nb077_alpha_dummy_063 x) ≠ (nb077_alpha_dummy_064 x) := by
  simpa only [nb077_alpha_dummy_063, nb077_alpha_dummy_064] using
    (freshVar_injective (((syn_ccnv (syn_c1st))).fv ∪ ((syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_324 (F : Class) (I : Class) : (nb077_alpha_dummy_057 F I) ∉ (((syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))).fv ∪ ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv) := by
  simpa only [nb077_alpha_dummy_057] using freshVar_not_mem (((syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)))).fv ∪ ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv) 0

theorem nb077_fresh_325 (x : Var) (F : Class) : (nb077_alpha_dummy_058 x F) ∉ (((syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))).fv ∪ ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv) := by
  simpa only [nb077_alpha_dummy_058] using freshVar_not_mem (((syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)))).fv ∪ ((syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd)))).fv) 0

theorem nb077_fresh_326 (F : Class) (I : Class) : (nb077_alpha_dummy_023 F I) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_023] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_327 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_024 x F I) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_024] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_328 (F : Class) (I : Class) : (nb077_alpha_dummy_071 F I) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_071] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_329 (x : Var) : (nb077_alpha_dummy_072 x) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_072] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_330 (F : Class) (I : Class) : (nb077_alpha_dummy_107 F I) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_107] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_331 (x : Var) : (nb077_alpha_dummy_108 x) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_108] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_332 (F : Class) (I : Class) : (nb077_alpha_dummy_151 F I) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_151] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_333 (x : Var) : (nb077_alpha_dummy_152 x) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_152] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_334 (F : Class) (I : Class) : (nb077_alpha_dummy_187 F I) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_187] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_335 (x : Var) : (nb077_alpha_dummy_188 x) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_188] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_336 (F : Class) (I : Class) : (nb077_alpha_dummy_223 F I) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_223] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_337 (x : Var) : (nb077_alpha_dummy_224 x) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_224] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_338 (F : Class) (I : Class) : (nb077_alpha_dummy_263 F I) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_263] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_339 (x : Var) : (nb077_alpha_dummy_264 x) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_264] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_340 (F : Class) (I : Class) : (nb077_alpha_dummy_315 F I) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_315] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_341 (x : Var) : (nb077_alpha_dummy_316 x) ∉ (((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb077_alpha_dummy_316] using freshVar_not_mem (((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb077_fresh_342 (F : Class) (I : Class) : (nb077_alpha_dummy_043 F I) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_034 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_035 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_043] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_034 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_035 F I)))).fv) 0

theorem nb077_fresh_343 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_044 x F I) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_037 x F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) := by
  simpa only [nb077_alpha_dummy_044] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_037 x F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) 0

theorem nb077_fresh_344 (F : Class) (I : Class) : (nb077_alpha_dummy_091 F I) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_082 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_083 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_091] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_082 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_083 F I)))).fv) 0

theorem nb077_fresh_345 (x : Var) : (nb077_alpha_dummy_092 x) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_085 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_086 x)))).fv) := by
  simpa only [nb077_alpha_dummy_092] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_085 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_086 x)))).fv) 0

theorem nb077_fresh_346 (F : Class) (I : Class) : (nb077_alpha_dummy_127 F I) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_118 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_119 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_127] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_118 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_119 F I)))).fv) 0

theorem nb077_fresh_347 (x : Var) : (nb077_alpha_dummy_128 x) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_121 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_122 x)))).fv) := by
  simpa only [nb077_alpha_dummy_128] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_121 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_122 x)))).fv) 0

theorem nb077_fresh_348 (F : Class) (I : Class) : (nb077_alpha_dummy_171 F I) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_162 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_163 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_171] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_162 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_163 F I)))).fv) 0

theorem nb077_fresh_349 (x : Var) : (nb077_alpha_dummy_172 x) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_165 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_166 x)))).fv) := by
  simpa only [nb077_alpha_dummy_172] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_165 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_166 x)))).fv) 0

theorem nb077_fresh_350 (F : Class) (I : Class) : (nb077_alpha_dummy_207 F I) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_198 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_199 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_207] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_198 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_199 F I)))).fv) 0

theorem nb077_fresh_351 (x : Var) : (nb077_alpha_dummy_208 x) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_201 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_202 x)))).fv) := by
  simpa only [nb077_alpha_dummy_208] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_201 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_202 x)))).fv) 0

theorem nb077_fresh_352 (F : Class) (I : Class) : (nb077_alpha_dummy_243 F I) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_234 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_235 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_243] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_234 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_235 F I)))).fv) 0

theorem nb077_fresh_353 (x : Var) : (nb077_alpha_dummy_244 x) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_237 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_238 x)))).fv) := by
  simpa only [nb077_alpha_dummy_244] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_237 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_238 x)))).fv) 0

theorem nb077_fresh_354 (F : Class) (I : Class) : (nb077_alpha_dummy_283 F I) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_274 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_275 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_283] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_274 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_275 F I)))).fv) 0

theorem nb077_fresh_355 (x : Var) : (nb077_alpha_dummy_284 x) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_277 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_278 x)))).fv) := by
  simpa only [nb077_alpha_dummy_284] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_277 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_278 x)))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
