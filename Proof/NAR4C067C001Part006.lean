import NAR4C067C001Part005

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

theorem nb067_fresh_371 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_068 x y f) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_061 x y f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) := by
  simpa only [nb067_alpha_dummy_068] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_061 x y f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) 0

theorem nb067_fresh_372 : (nb067_alpha_dummy_115) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_106)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_107)))).fv) := by
  simpa only [nb067_alpha_dummy_115] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_106)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_107)))).fv) 0

theorem nb067_fresh_373 (f : Var) : (nb067_alpha_dummy_116 f) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_109 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_110 f)))).fv) := by
  simpa only [nb067_alpha_dummy_116] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_109 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_110 f)))).fv) 0

theorem nb067_fresh_374 : (nb067_alpha_dummy_151) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_142)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_143)))).fv) := by
  simpa only [nb067_alpha_dummy_151] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_142)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_143)))).fv) 0

theorem nb067_fresh_375 (f : Var) : (nb067_alpha_dummy_152 f) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_145 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_146 f)))).fv) := by
  simpa only [nb067_alpha_dummy_152] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_145 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_146 f)))).fv) 0

theorem nb067_fresh_376 : (nb067_alpha_dummy_193) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_184)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_185)))).fv) := by
  simpa only [nb067_alpha_dummy_193] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_184)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_185)))).fv) 0

theorem nb067_fresh_377 (f : Var) : (nb067_alpha_dummy_194 f) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_187 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_188 f)))).fv) := by
  simpa only [nb067_alpha_dummy_194] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_187 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_188 f)))).fv) 0

theorem nb067_fresh_378 : (nb067_alpha_dummy_229) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_220)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_221)))).fv) := by
  simpa only [nb067_alpha_dummy_229] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_220)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_221)))).fv) 0

theorem nb067_fresh_379 (f : Var) : (nb067_alpha_dummy_230 f) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_223 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_224 f)))).fv) := by
  simpa only [nb067_alpha_dummy_230] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_223 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_224 f)))).fv) 0

theorem nb067_fresh_380 : (nb067_alpha_dummy_265) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_256)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_257)))).fv) := by
  simpa only [nb067_alpha_dummy_265] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_256)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_257)))).fv) 0

theorem nb067_fresh_381 (f : Var) : (nb067_alpha_dummy_266 f) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_259 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_260 f)))).fv) := by
  simpa only [nb067_alpha_dummy_266] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_259 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_260 f)))).fv) 0

theorem nb067_fresh_382 : (nb067_alpha_dummy_305) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_296)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_297)))).fv) := by
  simpa only [nb067_alpha_dummy_305] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_296)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_297)))).fv) 0

theorem nb067_fresh_383 (f : Var) : (nb067_alpha_dummy_306 f) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_299 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_300 f)))).fv) := by
  simpa only [nb067_alpha_dummy_306] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_299 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_300 f)))).fv) 0

theorem nb067_fresh_384 : (nb067_alpha_dummy_349) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_340)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_341)))).fv) := by
  simpa only [nb067_alpha_dummy_349] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_340)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_341)))).fv) 0

theorem nb067_fresh_385 (f : Var) : (nb067_alpha_dummy_350 f) ∉ (((syn_ccompl (Class.cv (nb067_alpha_dummy_343 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_344 f)))).fv) := by
  simpa only [nb067_alpha_dummy_350] using freshVar_not_mem (((syn_ccompl (Class.cv (nb067_alpha_dummy_343 f)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_344 f)))).fv) 0

theorem nb067_fresh_386 : (nb067_alpha_dummy_075) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_008))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_075] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_008))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_387 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_076 x y f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_076] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_388 : (nb067_alpha_dummy_047) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_016))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_047] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_016))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_389 (x : Var) (y : Var) : (nb067_alpha_dummy_048 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_048] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_390 : (nb067_alpha_dummy_123) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_092))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_123] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_092))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_391 (f : Var) : (nb067_alpha_dummy_124 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_124] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_094 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_392 : (nb067_alpha_dummy_159) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_128))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_159] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_128))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_393 (f : Var) : (nb067_alpha_dummy_160 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_160] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_130 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_394 : (nb067_alpha_dummy_201) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_170))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_201] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_170))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_395 (f : Var) : (nb067_alpha_dummy_202 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_202] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_172 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_396 : (nb067_alpha_dummy_237) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_206))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_237] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_206))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_397 (f : Var) : (nb067_alpha_dummy_238 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_238] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_398 : (nb067_alpha_dummy_273) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_242))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_273] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_242))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_399 (f : Var) : (nb067_alpha_dummy_274 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_274] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_244 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_400 : (nb067_alpha_dummy_313) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_282))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_313] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_282))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_401 (f : Var) : (nb067_alpha_dummy_314 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_314] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_284 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_402 : (nb067_alpha_dummy_357) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_326))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_357] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_326))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_403 (f : Var) : (nb067_alpha_dummy_358 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb067_alpha_dummy_358] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb067_alpha_dummy_328 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb067_fresh_404 : (nb067_alpha_dummy_035) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv) := by
  simpa only [nb067_alpha_dummy_035] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv) 0

theorem nb067_fresh_405 (x : Var) (y : Var) : (nb067_alpha_dummy_036 x y) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))).fv) := by
  simpa only [nb067_alpha_dummy_036] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))).fv) 0

theorem nb067_fresh_406 : (nb067_alpha_dummy_063) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv) := by
  simpa only [nb067_alpha_dummy_063] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))).fv) 0

theorem nb067_fresh_407 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_064 x y f) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) := by
  simpa only [nb067_alpha_dummy_064] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_061 x y f)) (Class.cv (nb067_alpha_dummy_062 x y f)))).fv) 0

theorem nb067_fresh_408 : (nb067_alpha_dummy_111) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv) := by
  simpa only [nb067_alpha_dummy_111] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))).fv) 0

theorem nb067_fresh_409 (f : Var) : (nb067_alpha_dummy_112 f) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv) := by
  simpa only [nb067_alpha_dummy_112] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_109 f)) (Class.cv (nb067_alpha_dummy_110 f)))).fv) 0

theorem nb067_fresh_410 : (nb067_alpha_dummy_147) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv) := by
  simpa only [nb067_alpha_dummy_147] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))).fv) 0

theorem nb067_fresh_411 (f : Var) : (nb067_alpha_dummy_148 f) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv) := by
  simpa only [nb067_alpha_dummy_148] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_145 f)) (Class.cv (nb067_alpha_dummy_146 f)))).fv) 0

theorem nb067_fresh_412 : (nb067_alpha_dummy_189) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv) := by
  simpa only [nb067_alpha_dummy_189] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))).fv) 0

theorem nb067_fresh_413 (f : Var) : (nb067_alpha_dummy_190 f) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv) := by
  simpa only [nb067_alpha_dummy_190] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))).fv) 0

theorem nb067_fresh_414 : (nb067_alpha_dummy_225) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv) := by
  simpa only [nb067_alpha_dummy_225] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))).fv) 0

theorem nb067_fresh_415 (f : Var) : (nb067_alpha_dummy_226 f) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv) := by
  simpa only [nb067_alpha_dummy_226] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_223 f)) (Class.cv (nb067_alpha_dummy_224 f)))).fv) 0

theorem nb067_fresh_416 : (nb067_alpha_dummy_261) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv) := by
  simpa only [nb067_alpha_dummy_261] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))).fv) 0

theorem nb067_fresh_417 (f : Var) : (nb067_alpha_dummy_262 f) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv) := by
  simpa only [nb067_alpha_dummy_262] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_259 f)) (Class.cv (nb067_alpha_dummy_260 f)))).fv) 0

theorem nb067_fresh_418 : (nb067_alpha_dummy_301) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv) := by
  simpa only [nb067_alpha_dummy_301] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))).fv) 0

theorem nb067_fresh_419 (f : Var) : (nb067_alpha_dummy_302 f) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv) := by
  simpa only [nb067_alpha_dummy_302] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))).fv) 0

theorem nb067_fresh_420 : (nb067_alpha_dummy_345) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv) := by
  simpa only [nb067_alpha_dummy_345] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))).fv) 0

theorem nb067_fresh_421 (f : Var) : (nb067_alpha_dummy_346 f) ∉ (((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv) := by
  simpa only [nb067_alpha_dummy_346] using freshVar_not_mem (((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))).fv) 0

theorem nb067_fresh_422 : (nb067_alpha_dummy_079) ∉ (((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv) := by
  simpa only [nb067_alpha_dummy_079] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb067_alpha_dummy_000)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000)))) (syn_cid))).fv) 0

theorem nb067_fresh_423 (f : Var) : (nb067_alpha_dummy_080 f) ∉ (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) := by
  simpa only [nb067_alpha_dummy_080] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0

theorem nb067_fresh_424 : (nb067_alpha_dummy_317) ∉ (((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_001)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_001)))).fv) := by
  simpa only [nb067_alpha_dummy_317] using freshVar_not_mem (((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_001)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_001)))).fv) 0

theorem nb067_fresh_425 (x : Var) (f : Var) : (nb067_alpha_dummy_318 x f) ∉ (((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv ∪ ((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv) := by
  simpa only [nb067_alpha_dummy_318] using freshVar_not_mem (((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv ∪ ((syn_cnin (syn_crn (Class.cv f)) (Class.cv x))).fv) 0

theorem nb067_fresh_426 : (nb067_alpha_dummy_007) ∉ (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) := by
  simpa only [nb067_alpha_dummy_007] using freshVar_not_mem (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) 0

theorem nb067_fresh_427 : (nb067_alpha_dummy_008) ∉ (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) := by
  simpa only [nb067_alpha_dummy_008] using freshVar_not_mem (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) 1

theorem nb067_distinct_428 : (nb067_alpha_dummy_007) ≠ (nb067_alpha_dummy_008) := by
  simpa only [nb067_alpha_dummy_007, nb067_alpha_dummy_008] using
    (freshVar_injective (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_429 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_009 x y f) ∉ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) := by
  simpa only [nb067_alpha_dummy_009] using freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) 0

theorem nb067_fresh_430 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_010 x y f) ∉ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) := by
  simpa only [nb067_alpha_dummy_010] using freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) 1

theorem nb067_distinct_431 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_009 x y f) ≠ (nb067_alpha_dummy_010 x y f) := by
  simpa only [nb067_alpha_dummy_009, nb067_alpha_dummy_010] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_432 : (nb067_alpha_dummy_077) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv) := by
  simpa only [nb067_alpha_dummy_077] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_008)))).fv) 0

theorem nb067_fresh_433 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_078 x y f) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv) := by
  simpa only [nb067_alpha_dummy_078] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))).fv) 0

theorem nb067_fresh_434 : (nb067_alpha_dummy_049) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv) := by
  simpa only [nb067_alpha_dummy_049] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_016)))).fv) 0

theorem nb067_fresh_435 (x : Var) (y : Var) : (nb067_alpha_dummy_050 x y) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv) := by
  simpa only [nb067_alpha_dummy_050] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))).fv) 0

theorem nb067_fresh_436 : (nb067_alpha_dummy_125) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv) := by
  simpa only [nb067_alpha_dummy_125] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_092)))).fv) 0

theorem nb067_fresh_437 (f : Var) : (nb067_alpha_dummy_126 f) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv) := by
  simpa only [nb067_alpha_dummy_126] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))).fv) 0

theorem nb067_fresh_438 : (nb067_alpha_dummy_161) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv) := by
  simpa only [nb067_alpha_dummy_161] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_128)))).fv) 0

theorem nb067_fresh_439 (f : Var) : (nb067_alpha_dummy_162 f) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv) := by
  simpa only [nb067_alpha_dummy_162] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))).fv) 0

theorem nb067_fresh_440 : (nb067_alpha_dummy_203) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv) := by
  simpa only [nb067_alpha_dummy_203] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_170)))).fv) 0

theorem nb067_fresh_441 (f : Var) : (nb067_alpha_dummy_204 f) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv) := by
  simpa only [nb067_alpha_dummy_204] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))).fv) 0

theorem nb067_fresh_442 : (nb067_alpha_dummy_239) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv) := by
  simpa only [nb067_alpha_dummy_239] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_206)))).fv) 0

theorem nb067_fresh_443 (f : Var) : (nb067_alpha_dummy_240 f) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv) := by
  simpa only [nb067_alpha_dummy_240] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_208 f)))).fv) 0

theorem nb067_fresh_444 : (nb067_alpha_dummy_275) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv) := by
  simpa only [nb067_alpha_dummy_275] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_242)))).fv) 0

theorem nb067_fresh_445 (f : Var) : (nb067_alpha_dummy_276 f) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv) := by
  simpa only [nb067_alpha_dummy_276] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_244 f)))).fv) 0

theorem nb067_fresh_446 : (nb067_alpha_dummy_315) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv) := by
  simpa only [nb067_alpha_dummy_315] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_282)))).fv) 0

theorem nb067_fresh_447 (f : Var) : (nb067_alpha_dummy_316 f) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv) := by
  simpa only [nb067_alpha_dummy_316] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))).fv) 0

theorem nb067_fresh_448 : (nb067_alpha_dummy_359) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv) := by
  simpa only [nb067_alpha_dummy_359] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_326)))).fv) 0

theorem nb067_fresh_449 (f : Var) : (nb067_alpha_dummy_360 f) ∉ (((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv) := by
  simpa only [nb067_alpha_dummy_360] using freshVar_not_mem (((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv ∪ ((syn_cphi (Class.cv (nb067_alpha_dummy_328 f)))).fv) 0

theorem nb067_fresh_450 : (nb067_alpha_dummy_319) ∉ (((syn_crn (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((Class.cv (nb067_alpha_dummy_001))).fv) := by
  simpa only [nb067_alpha_dummy_319] using freshVar_not_mem (((syn_crn (Class.cv (nb067_alpha_dummy_000)))).fv ∪ ((Class.cv (nb067_alpha_dummy_001))).fv) 0

theorem nb067_fresh_451 (x : Var) (f : Var) : (nb067_alpha_dummy_320 x f) ∉ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb067_alpha_dummy_320] using freshVar_not_mem (((syn_crn (Class.cv f))).fv ∪ ((Class.cv x)).fv) 0

theorem nb067_fresh_452 : (nb067_alpha_dummy_003) ∉ (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))).fv) := by
  simpa only [nb067_alpha_dummy_003] using freshVar_not_mem (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))).fv) 0

theorem nb067_fresh_453 : (nb067_alpha_dummy_005) ∉ (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv)) (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))))).fv) := by
  simpa only [nb067_alpha_dummy_005] using freshVar_not_mem (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv)) (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))))).fv) 0

theorem nb067_fresh_454 : (nb067_alpha_dummy_089) ∉ (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv) := by
  simpa only [nb067_alpha_dummy_089] using freshVar_not_mem (({(nb067_alpha_dummy_083)} : Finset Var) ∪ ({(nb067_alpha_dummy_084)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_085) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_083)) (syn_ccnv (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_085))) (syn_wbr (Class.cv (nb067_alpha_dummy_085)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_084)))))).fv) 0

theorem nb067_fresh_455 (f : Var) : (nb067_alpha_dummy_090 f) ∉ (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb067_alpha_dummy_088 f))) (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_087 f)))))).fv) := by
  simpa only [nb067_alpha_dummy_090] using freshVar_not_mem (({(nb067_alpha_dummy_086 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_087 f)} : Finset Var) ∪ ((syn_wex (nb067_alpha_dummy_088 f) (syn_wa (syn_wbr (Class.cv (nb067_alpha_dummy_086 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb067_alpha_dummy_088 f))) (syn_wbr (Class.cv (nb067_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_087 f)))))).fv) 0

theorem nb067_fresh_456 : (nb067_alpha_dummy_167) ∉ (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_163)))).fv) := by
  simpa only [nb067_alpha_dummy_167] using freshVar_not_mem (({(nb067_alpha_dummy_163)} : Finset Var) ∪ ({(nb067_alpha_dummy_164)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_163)))).fv) 0

theorem nb067_fresh_457 (f : Var) : (nb067_alpha_dummy_168 f) ∉ (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_165 f)))).fv) := by
  simpa only [nb067_alpha_dummy_168] using freshVar_not_mem (({(nb067_alpha_dummy_165 f)} : Finset Var) ∪ ({(nb067_alpha_dummy_166 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f) (Class.cv (nb067_alpha_dummy_165 f)))).fv) 0

theorem nb067_fresh_458 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_004 x y f) ∉ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) := by
  simpa only [nb067_alpha_dummy_004] using freshVar_not_mem (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) 0

theorem nb067_fresh_459 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_006 x y f) ∉ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f)) (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) := by
  simpa only [nb067_alpha_dummy_006] using freshVar_not_mem (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f)) (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) 0

theorem nb067_fresh_460 : (nb067_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb067_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb067_fresh_461 : (nb067_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb067_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb067_fresh_462 : (nb067_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb067_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb067_distinct_463 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_001) := by
  simpa only [nb067_alpha_dummy_000, nb067_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_464 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_002) := by
  simpa only [nb067_alpha_dummy_000, nb067_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_465 : (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_002) := by
  simpa only [nb067_alpha_dummy_001, nb067_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb067_support_mem_0000 : (nb067_alpha_dummy_001) ∈ (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv)) (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0001 (x : Var) (y : Var) (f : Var) : x ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f)) (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0002 : (nb067_alpha_dummy_002) ∈ (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv)) (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0003 (x : Var) (y : Var) (f : Var) : y ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f)) (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0004 : (nb067_alpha_dummy_003) ∈ (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ({(nb067_alpha_dummy_003)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_001)) (syn_cvv)) (Wff.classMem (Class.cv (nb067_alpha_dummy_002)) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_003)) (Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0005 (x : Var) (y : Var) (f : Var) : (nb067_alpha_dummy_004 x y f) ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb067_alpha_dummy_004 x y f)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb067_alpha_dummy_004 x y f)) (Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0006 : (nb067_alpha_dummy_001) ∈ (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0007 (x : Var) (y : Var) (f : Var) : x ∈ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0008 : (nb067_alpha_dummy_001) ∈ (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0009 : (nb067_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003)) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0010 (x : Var) (y : Var) (f : Var) : x ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0011 (x : Var) (y : Var) (f : Var) : x ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (Class.cv (nb067_alpha_dummy_004 x y f)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0012 : (nb067_alpha_dummy_001) ∈ (((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008) (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))) (Wff.classEq (Class.cv (nb067_alpha_dummy_007)) (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0013 (x : Var) (y : Var) (f : Var) : x ∈ (((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f)) (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0014 : (nb067_alpha_dummy_001) ∈ (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0015 : (nb067_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0016 (x : Var) (y : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0017 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0018 : (nb067_alpha_dummy_001) ∈ (((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_015) (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_001)) (Wff.classEq (Class.cv (nb067_alpha_dummy_015)) (syn_cphi (Class.cv (nb067_alpha_dummy_016))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0019 (x : Var) (y : Var) : x ∈ (((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv ∪ ((Class.cab (nb067_alpha_dummy_017 x y) (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv x) (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y)) (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0020 : (nb067_alpha_dummy_016) ∈ (((Class.cv (nb067_alpha_dummy_016))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0021 (x : Var) (y : Var) : (nb067_alpha_dummy_018 x y) ∈ (((Class.cv (nb067_alpha_dummy_018 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0022 : (nb067_alpha_dummy_023) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_023)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_023)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_023))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0023 (x : Var) (y : Var) : (nb067_alpha_dummy_025 x y) ∈ (((Wff.classMem (Class.cv (nb067_alpha_dummy_025 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb067_alpha_dummy_025 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb067_alpha_dummy_025 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0024 : (nb067_alpha_dummy_023) ∈ (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0025 (x : Var) (y : Var) : (nb067_alpha_dummy_025 x y) ∈ (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0026 : (nb067_alpha_dummy_030) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0027 (x : Var) (y : Var) : (nb067_alpha_dummy_033 x y) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0028 : (nb067_alpha_dummy_030) ∈ (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0029 (x : Var) (y : Var) : (nb067_alpha_dummy_033 x y) ∈ (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_034 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0030 : (nb067_alpha_dummy_031) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0031 (x : Var) (y : Var) : (nb067_alpha_dummy_034 x y) ∈ (((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))).fv ∪ ((syn_cnin (Class.cv (nb067_alpha_dummy_033 x y)) (Class.cv (nb067_alpha_dummy_034 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0032 : (nb067_alpha_dummy_031) ∈ (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0033 (x : Var) (y : Var) : (nb067_alpha_dummy_034 x y) ∈ (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_034 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0034 : (nb067_alpha_dummy_030) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_030)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_031)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0035 (x : Var) (y : Var) : (nb067_alpha_dummy_033 x y) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_033 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_034 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0036 : (nb067_alpha_dummy_030) ∈ (((Class.cv (nb067_alpha_dummy_030))).fv ∪ ((Class.cv (nb067_alpha_dummy_030))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0037 (x : Var) (y : Var) : (nb067_alpha_dummy_033 x y) ∈ (((Class.cv (nb067_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_033 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0038 : (nb067_alpha_dummy_031) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_030)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_031)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0039 (x : Var) (y : Var) : (nb067_alpha_dummy_034 x y) ∈ (((syn_ccompl (Class.cv (nb067_alpha_dummy_033 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb067_alpha_dummy_034 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0040 : (nb067_alpha_dummy_031) ∈ (((Class.cv (nb067_alpha_dummy_031))).fv ∪ ((Class.cv (nb067_alpha_dummy_031))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0041 (x : Var) (y : Var) : (nb067_alpha_dummy_034 x y) ∈ (((Class.cv (nb067_alpha_dummy_034 x y))).fv ∪ ((Class.cv (nb067_alpha_dummy_034 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0042 : (nb067_alpha_dummy_002) ∈ (({(nb067_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb067_alpha_dummy_002)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((Class.cab (nb067_alpha_dummy_000) (syn_wf (Class.cv (nb067_alpha_dummy_000)) (Class.cv (nb067_alpha_dummy_002)) (Class.cv (nb067_alpha_dummy_001))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0043 (x : Var) (y : Var) (f : Var) : y ∈ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((Class.cab f (syn_wf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0044 : (nb067_alpha_dummy_002) ∈ (((syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))).fv ∪ ((Class.cv (nb067_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
