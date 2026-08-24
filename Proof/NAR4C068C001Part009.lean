import NAR4C068C001Part008

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

theorem nb068_fresh_608 : (nb068_alpha_dummy_223) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv) := by
  simpa only [nb068_alpha_dummy_223] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv) 0

theorem nb068_fresh_609 (f : Var) : (nb068_alpha_dummy_224 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv) := by
  simpa only [nb068_alpha_dummy_224] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv) 0

theorem nb068_fresh_610 : (nb068_alpha_dummy_263) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv) := by
  simpa only [nb068_alpha_dummy_263] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv) 0

theorem nb068_fresh_611 (f : Var) : (nb068_alpha_dummy_264 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv) := by
  simpa only [nb068_alpha_dummy_264] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv) 0

theorem nb068_fresh_612 : (nb068_alpha_dummy_307) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv) := by
  simpa only [nb068_alpha_dummy_307] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv) 0

theorem nb068_fresh_613 (f : Var) : (nb068_alpha_dummy_308 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv) := by
  simpa only [nb068_alpha_dummy_308] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv) 0

theorem nb068_fresh_614 : (nb068_alpha_dummy_355) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv) := by
  simpa only [nb068_alpha_dummy_355] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_350)) (Class.cv (nb068_alpha_dummy_351)))).fv) 0

theorem nb068_fresh_615 (f : Var) : (nb068_alpha_dummy_356 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_353 f)) (Class.cv (nb068_alpha_dummy_354 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_353 f)) (Class.cv (nb068_alpha_dummy_354 f)))).fv) := by
  simpa only [nb068_alpha_dummy_356] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_353 f)) (Class.cv (nb068_alpha_dummy_354 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_353 f)) (Class.cv (nb068_alpha_dummy_354 f)))).fv) 0

theorem nb068_fresh_616 : (nb068_alpha_dummy_391) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv) := by
  simpa only [nb068_alpha_dummy_391] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))).fv) 0

theorem nb068_fresh_617 (f : Var) : (nb068_alpha_dummy_392 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f)))).fv) := by
  simpa only [nb068_alpha_dummy_392] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f)))).fv) 0

theorem nb068_fresh_618 : (nb068_alpha_dummy_433) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv) := by
  simpa only [nb068_alpha_dummy_433] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))).fv) 0

theorem nb068_fresh_619 (f : Var) : (nb068_alpha_dummy_434 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f)))).fv) := by
  simpa only [nb068_alpha_dummy_434] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f)))).fv) 0

theorem nb068_fresh_620 : (nb068_alpha_dummy_469) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))).fv) := by
  simpa only [nb068_alpha_dummy_469] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_464)) (Class.cv (nb068_alpha_dummy_465)))).fv) 0

theorem nb068_fresh_621 (f : Var) : (nb068_alpha_dummy_470 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_467 f)) (Class.cv (nb068_alpha_dummy_468 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_467 f)) (Class.cv (nb068_alpha_dummy_468 f)))).fv) := by
  simpa only [nb068_alpha_dummy_470] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_467 f)) (Class.cv (nb068_alpha_dummy_468 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_467 f)) (Class.cv (nb068_alpha_dummy_468 f)))).fv) 0

theorem nb068_fresh_622 : (nb068_alpha_dummy_505) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv) := by
  simpa only [nb068_alpha_dummy_505] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv) 0

theorem nb068_fresh_623 (f : Var) : (nb068_alpha_dummy_506 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_503 f)) (Class.cv (nb068_alpha_dummy_504 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_503 f)) (Class.cv (nb068_alpha_dummy_504 f)))).fv) := by
  simpa only [nb068_alpha_dummy_506] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_503 f)) (Class.cv (nb068_alpha_dummy_504 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_503 f)) (Class.cv (nb068_alpha_dummy_504 f)))).fv) 0

theorem nb068_fresh_624 : (nb068_alpha_dummy_041) ∉ (((syn_cnin (syn_ccom (Class.cv (nb068_alpha_dummy_000)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb068_alpha_dummy_000)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv) := by
  simpa only [nb068_alpha_dummy_041] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv (nb068_alpha_dummy_000)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb068_alpha_dummy_000)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (syn_cid))).fv) 0

theorem nb068_fresh_625 (f : Var) : (nb068_alpha_dummy_042 f) ∉ (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) := by
  simpa only [nb068_alpha_dummy_042] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0

theorem nb068_fresh_626 : (nb068_alpha_dummy_323) ∉ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv) := by
  simpa only [nb068_alpha_dummy_323] using freshVar_not_mem (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv) 0

theorem nb068_fresh_627 (f : Var) : (nb068_alpha_dummy_324 f) ∉ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f)))) (syn_cid))).fv) := by
  simpa only [nb068_alpha_dummy_324] using freshVar_not_mem (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f)))) (syn_cid))).fv) 0

theorem nb068_fresh_628 : (nb068_alpha_dummy_279) ∉ (((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_002)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_002)))).fv) := by
  simpa only [nb068_alpha_dummy_279] using freshVar_not_mem (((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_002)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_002)))).fv) 0

theorem nb068_fresh_629 (y : Var) (f : Var) : (nb068_alpha_dummy_280 y f) ∉ (((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv ∪ ((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv) := by
  simpa only [nb068_alpha_dummy_280] using freshVar_not_mem (((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv ∪ ((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv) 0

theorem nb068_fresh_630 : (nb068_alpha_dummy_039) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv) := by
  simpa only [nb068_alpha_dummy_039] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv) 0

theorem nb068_fresh_631 (x : Var) (y : Var) : (nb068_alpha_dummy_040 x y) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv) := by
  simpa only [nb068_alpha_dummy_040] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv) 0

theorem nb068_fresh_632 : (nb068_alpha_dummy_087) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv) := by
  simpa only [nb068_alpha_dummy_087] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_054)))).fv) 0

theorem nb068_fresh_633 (f : Var) : (nb068_alpha_dummy_088 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv) := by
  simpa only [nb068_alpha_dummy_088] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))).fv) 0

theorem nb068_fresh_634 : (nb068_alpha_dummy_123) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv) := by
  simpa only [nb068_alpha_dummy_123] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_090)))).fv) 0

theorem nb068_fresh_635 (f : Var) : (nb068_alpha_dummy_124 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv) := by
  simpa only [nb068_alpha_dummy_124] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))).fv) 0

theorem nb068_fresh_636 : (nb068_alpha_dummy_165) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv) := by
  simpa only [nb068_alpha_dummy_165] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_132)))).fv) 0

theorem nb068_fresh_637 (f : Var) : (nb068_alpha_dummy_166 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv) := by
  simpa only [nb068_alpha_dummy_166] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))).fv) 0

theorem nb068_fresh_638 : (nb068_alpha_dummy_201) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv) := by
  simpa only [nb068_alpha_dummy_201] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_168)))).fv) 0

theorem nb068_fresh_639 (f : Var) : (nb068_alpha_dummy_202 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv) := by
  simpa only [nb068_alpha_dummy_202] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))).fv) 0

theorem nb068_fresh_640 : (nb068_alpha_dummy_237) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv) := by
  simpa only [nb068_alpha_dummy_237] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv) 0

theorem nb068_fresh_641 (f : Var) : (nb068_alpha_dummy_238 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv) := by
  simpa only [nb068_alpha_dummy_238] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv) 0

theorem nb068_fresh_642 : (nb068_alpha_dummy_277) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv) := by
  simpa only [nb068_alpha_dummy_277] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv) 0

theorem nb068_fresh_643 (f : Var) : (nb068_alpha_dummy_278 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv) := by
  simpa only [nb068_alpha_dummy_278] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv) 0

theorem nb068_fresh_644 : (nb068_alpha_dummy_321) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv) := by
  simpa only [nb068_alpha_dummy_321] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv) 0

theorem nb068_fresh_645 (f : Var) : (nb068_alpha_dummy_322 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv) := by
  simpa only [nb068_alpha_dummy_322] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv) 0

theorem nb068_fresh_646 : (nb068_alpha_dummy_369) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv) := by
  simpa only [nb068_alpha_dummy_369] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_336)))).fv) 0

theorem nb068_fresh_647 (f : Var) : (nb068_alpha_dummy_370 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv) := by
  simpa only [nb068_alpha_dummy_370] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))).fv) 0

theorem nb068_fresh_648 : (nb068_alpha_dummy_405) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv) := by
  simpa only [nb068_alpha_dummy_405] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_372)))).fv) 0

theorem nb068_fresh_649 (f : Var) : (nb068_alpha_dummy_406 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv) := by
  simpa only [nb068_alpha_dummy_406] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))).fv) 0

theorem nb068_fresh_650 : (nb068_alpha_dummy_447) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv) := by
  simpa only [nb068_alpha_dummy_447] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_414)))).fv) 0

theorem nb068_fresh_651 (f : Var) : (nb068_alpha_dummy_448 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv) := by
  simpa only [nb068_alpha_dummy_448] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))).fv) 0

theorem nb068_fresh_652 : (nb068_alpha_dummy_483) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv) := by
  simpa only [nb068_alpha_dummy_483] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv) 0

theorem nb068_fresh_653 (f : Var) : (nb068_alpha_dummy_484 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv) := by
  simpa only [nb068_alpha_dummy_484] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv) 0

theorem nb068_fresh_654 : (nb068_alpha_dummy_519) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv) := by
  simpa only [nb068_alpha_dummy_519] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv) 0

theorem nb068_fresh_655 (f : Var) : (nb068_alpha_dummy_520 f) ∉ (((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv) := by
  simpa only [nb068_alpha_dummy_520] using freshVar_not_mem (((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv) 0

theorem nb068_fresh_656 : (nb068_alpha_dummy_281) ∉ (((syn_crn (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) := by
  simpa only [nb068_alpha_dummy_281] using freshVar_not_mem (((syn_crn (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) 0

theorem nb068_fresh_657 (y : Var) (f : Var) : (nb068_alpha_dummy_282 y f) ∉ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb068_alpha_dummy_282] using freshVar_not_mem (((syn_crn (Class.cv f))).fv ∪ ((Class.cv y)).fv) 0

theorem nb068_fresh_658 : (nb068_alpha_dummy_003) ∉ (({(nb068_alpha_dummy_001)} : Finset Var) ∪ ({(nb068_alpha_dummy_002)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_000) (syn_wf1o (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_001)) (Class.cv (nb068_alpha_dummy_002))))).fv) := by
  simpa only [nb068_alpha_dummy_003] using freshVar_not_mem (({(nb068_alpha_dummy_001)} : Finset Var) ∪ ({(nb068_alpha_dummy_002)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_000) (syn_wf1o (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_001)) (Class.cv (nb068_alpha_dummy_002))))).fv) 0

theorem nb068_fresh_659 : (nb068_alpha_dummy_051) ∉ (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_047))) (syn_wbr (Class.cv (nb068_alpha_dummy_047)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_046)))))).fv) := by
  simpa only [nb068_alpha_dummy_051] using freshVar_not_mem (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_047))) (syn_wbr (Class.cv (nb068_alpha_dummy_047)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_046)))))).fv) 0

theorem nb068_fresh_660 (f : Var) : (nb068_alpha_dummy_052 f) ∉ (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_050 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_049 f)))))).fv) := by
  simpa only [nb068_alpha_dummy_052] using freshVar_not_mem (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_050 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_049 f)))))).fv) 0

theorem nb068_fresh_661 : (nb068_alpha_dummy_129) ∉ (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_125)))).fv) := by
  simpa only [nb068_alpha_dummy_129] using freshVar_not_mem (({(nb068_alpha_dummy_125)} : Finset Var) ∪ ({(nb068_alpha_dummy_126)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_125)))).fv) 0

theorem nb068_fresh_662 (f : Var) : (nb068_alpha_dummy_130 f) ∉ (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_127 f)))).fv) := by
  simpa only [nb068_alpha_dummy_130] using freshVar_not_mem (({(nb068_alpha_dummy_127 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_128 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_127 f)))).fv) 0

theorem nb068_fresh_663 : (nb068_alpha_dummy_333) ∉ (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327)) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_328)))))).fv) := by
  simpa only [nb068_alpha_dummy_333] using freshVar_not_mem (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327)) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_328)))))).fv) 0

theorem nb068_fresh_664 (f : Var) : (nb068_alpha_dummy_334 f) ∉ (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_330 f)) (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_331 f)))))).fv) := by
  simpa only [nb068_alpha_dummy_334] using freshVar_not_mem (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_330 f)) (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_331 f)))))).fv) 0

theorem nb068_fresh_665 : (nb068_alpha_dummy_411) ∉ (({(nb068_alpha_dummy_407)} : Finset Var) ∪ ({(nb068_alpha_dummy_408)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_408)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_407)))).fv) := by
  simpa only [nb068_alpha_dummy_411] using freshVar_not_mem (({(nb068_alpha_dummy_407)} : Finset Var) ∪ ({(nb068_alpha_dummy_408)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_408)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_407)))).fv) 0

theorem nb068_fresh_666 (f : Var) : (nb068_alpha_dummy_412 f) ∉ (({(nb068_alpha_dummy_409 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_410 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_409 f)))).fv) := by
  simpa only [nb068_alpha_dummy_412] using freshVar_not_mem (({(nb068_alpha_dummy_409 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_410 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_409 f)))).fv) 0

theorem nb068_fresh_667 (x : Var) (y : Var) (f : Var) : (nb068_alpha_dummy_004 x y f) ∉ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wex f (syn_wf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) := by
  simpa only [nb068_alpha_dummy_004] using freshVar_not_mem (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wex f (syn_wf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) 0

theorem nb068_fresh_668 : (nb068_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb068_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb068_fresh_669 : (nb068_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb068_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb068_fresh_670 : (nb068_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb068_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb068_distinct_671 : (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_001) := by
  simpa only [nb068_alpha_dummy_000, nb068_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_672 : (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_002) := by
  simpa only [nb068_alpha_dummy_000, nb068_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_673 : (nb068_alpha_dummy_001) ≠ (nb068_alpha_dummy_002) := by
  simpa only [nb068_alpha_dummy_001, nb068_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb068_support_mem_0000 : (nb068_alpha_dummy_001) ∈ (({(nb068_alpha_dummy_001)} : Finset Var) ∪ ({(nb068_alpha_dummy_002)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_000) (syn_wf1o (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_001)) (Class.cv (nb068_alpha_dummy_002))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0001 (x : Var) (y : Var) (f : Var) : x ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wex f (syn_wf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0002 : (nb068_alpha_dummy_002) ∈ (({(nb068_alpha_dummy_001)} : Finset Var) ∪ ({(nb068_alpha_dummy_002)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_000) (syn_wf1o (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_001)) (Class.cv (nb068_alpha_dummy_002))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0003 (x : Var) (y : Var) (f : Var) : y ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ((syn_wex f (syn_wf1o (Class.cv f) (Class.cv x) (Class.cv y)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0004 : (nb068_alpha_dummy_001) ∈ (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0005 : (nb068_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0006 (x : Var) (y : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0007 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0008 : (nb068_alpha_dummy_001) ∈ (((Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cphi (Class.cv (nb068_alpha_dummy_006))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0009 (x : Var) (y : Var) : x ∈ (((Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0006 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0010 : (nb068_alpha_dummy_006) ∈ (((Class.cv (nb068_alpha_dummy_006))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0011 (x : Var) (y : Var) : (nb068_alpha_dummy_008 x y) ∈ (((Class.cv (nb068_alpha_dummy_008 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0012 : (nb068_alpha_dummy_013) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_013)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_013)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_013))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0013 (x : Var) (y : Var) : (nb068_alpha_dummy_015 x y) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_015 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_015 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_015 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0014 : (nb068_alpha_dummy_013) ∈ (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0015 (x : Var) (y : Var) : (nb068_alpha_dummy_015 x y) ∈ (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0016 : (nb068_alpha_dummy_020) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0017 (x : Var) (y : Var) : (nb068_alpha_dummy_023 x y) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0018 : (nb068_alpha_dummy_020) ∈ (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0019 (x : Var) (y : Var) : (nb068_alpha_dummy_023 x y) ∈ (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪ ((Class.cv (nb068_alpha_dummy_024 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0020 : (nb068_alpha_dummy_021) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0021 (x : Var) (y : Var) : (nb068_alpha_dummy_024 x y) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0022 : (nb068_alpha_dummy_021) ∈ (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0023 (x : Var) (y : Var) : (nb068_alpha_dummy_024 x y) ∈ (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪ ((Class.cv (nb068_alpha_dummy_024 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0024 : (nb068_alpha_dummy_020) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_021)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0025 (x : Var) (y : Var) : (nb068_alpha_dummy_023 x y) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_023 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_024 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0026 : (nb068_alpha_dummy_020) ∈ (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_020))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0027 (x : Var) (y : Var) : (nb068_alpha_dummy_023 x y) ∈ (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪ ((Class.cv (nb068_alpha_dummy_023 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0028 : (nb068_alpha_dummy_021) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_021)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0029 (x : Var) (y : Var) : (nb068_alpha_dummy_024 x y) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_023 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_024 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0030 : (nb068_alpha_dummy_021) ∈ (((Class.cv (nb068_alpha_dummy_021))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0031 (x : Var) (y : Var) : (nb068_alpha_dummy_024 x y) ∈ (((Class.cv (nb068_alpha_dummy_024 x y))).fv ∪ ((Class.cv (nb068_alpha_dummy_024 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0032 : (nb068_alpha_dummy_002) ∈ (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0033 : (nb068_alpha_dummy_002) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0034 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0035 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0036 : (nb068_alpha_dummy_002) ∈ (((Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0037 (x : Var) (y : Var) : y ∈ (((Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0034 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0038 : (nb068_alpha_dummy_006) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0039 (x : Var) (y : Var) : (nb068_alpha_dummy_008 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0040 : (nb068_alpha_dummy_006) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_006)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0041 (x : Var) (y : Var) : (nb068_alpha_dummy_008 x y) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0042 : (nb068_alpha_dummy_045) ∈ (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_047))) (syn_wbr (Class.cv (nb068_alpha_dummy_047)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_046)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0043 (f : Var) : (nb068_alpha_dummy_048 f) ∈ (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_050 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_049 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0044 : (nb068_alpha_dummy_046) ∈ (({(nb068_alpha_dummy_045)} : Finset Var) ∪ ({(nb068_alpha_dummy_046)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_047) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_045)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_047))) (syn_wbr (Class.cv (nb068_alpha_dummy_047)) (Class.cv (nb068_alpha_dummy_000)) (Class.cv (nb068_alpha_dummy_046)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0045 (f : Var) : (nb068_alpha_dummy_049 f) ∈ (({(nb068_alpha_dummy_048 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_049 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_050 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_048 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_050 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_050 f)) (Class.cv f) (Class.cv (nb068_alpha_dummy_049 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0046 : (nb068_alpha_dummy_045) ∈ (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0047 : (nb068_alpha_dummy_045) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cphi (Class.cv (nb068_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0048 (f : Var) : (nb068_alpha_dummy_048 f) ∈ (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0049 (f : Var) : (nb068_alpha_dummy_048 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0050 : (nb068_alpha_dummy_045) ∈ (((Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cphi (Class.cv (nb068_alpha_dummy_054))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cphi (Class.cv (nb068_alpha_dummy_054))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0046) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0051 (f : Var) : (nb068_alpha_dummy_048 f) ∈ (((Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0048 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0052 : (nb068_alpha_dummy_054) ∈ (((Class.cv (nb068_alpha_dummy_054))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0053 (f : Var) : (nb068_alpha_dummy_056 f) ∈ (((Class.cv (nb068_alpha_dummy_056 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0054 : (nb068_alpha_dummy_061) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_061)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_061)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_061))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0055 (f : Var) : (nb068_alpha_dummy_063 f) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_063 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_063 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_063 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0056 : (nb068_alpha_dummy_061) ∈ (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0057 (f : Var) : (nb068_alpha_dummy_063 f) ∈ (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0058 : (nb068_alpha_dummy_068) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0059 (f : Var) : (nb068_alpha_dummy_071 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0060 : (nb068_alpha_dummy_068) ∈ (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0061 (f : Var) : (nb068_alpha_dummy_071 f) ∈ (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0062 : (nb068_alpha_dummy_069) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0063 (f : Var) : (nb068_alpha_dummy_072 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0064 : (nb068_alpha_dummy_069) ∈ (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0065 (f : Var) : (nb068_alpha_dummy_072 f) ∈ (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0066 : (nb068_alpha_dummy_068) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_068)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_069)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0067 (f : Var) : (nb068_alpha_dummy_071 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_071 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_072 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0068 : (nb068_alpha_dummy_068) ∈ (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_068))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0069 (f : Var) : (nb068_alpha_dummy_071 f) ∈ (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_071 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0070 : (nb068_alpha_dummy_069) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_068)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_069)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0071 (f : Var) : (nb068_alpha_dummy_072 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_071 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_072 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0072 : (nb068_alpha_dummy_069) ∈ (((Class.cv (nb068_alpha_dummy_069))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0073 (f : Var) : (nb068_alpha_dummy_072 f) ∈ (((Class.cv (nb068_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0074 : (nb068_alpha_dummy_046) ∈ (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0075 : (nb068_alpha_dummy_046) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cphi (Class.cv (nb068_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
