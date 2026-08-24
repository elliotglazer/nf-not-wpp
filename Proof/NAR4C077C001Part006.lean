import NAR4C077C001Part005

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

theorem nb077_fresh_356 (F : Class) (I : Class) : (nb077_alpha_dummy_305 F I) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_296 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_297 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_305] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_296 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_297 F I)))).fv) 0

theorem nb077_fresh_357 (x : Var) : (nb077_alpha_dummy_306 x) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_299 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_300 x)))).fv) := by
  simpa only [nb077_alpha_dummy_306] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_299 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_300 x)))).fv) 0

theorem nb077_fresh_358 (F : Class) (I : Class) : (nb077_alpha_dummy_335 F I) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_326 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_327 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_335] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_326 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_327 F I)))).fv) 0

theorem nb077_fresh_359 (x : Var) : (nb077_alpha_dummy_336 x) ∉ (((syn_ccompl (Class.cv (nb077_alpha_dummy_329 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_330 x)))).fv) := by
  simpa only [nb077_alpha_dummy_336] using freshVar_not_mem (((syn_ccompl (Class.cv (nb077_alpha_dummy_329 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_330 x)))).fv) 0

theorem nb077_fresh_360 (F : Class) (I : Class) : (nb077_alpha_dummy_051 F I) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_051] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_361 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_052 x F I) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_052] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_362 (F : Class) (I : Class) : (nb077_alpha_dummy_099 F I) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_099] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_363 (x : Var) : (nb077_alpha_dummy_100 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_100] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_364 (F : Class) (I : Class) : (nb077_alpha_dummy_135 F I) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_135] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_365 (x : Var) : (nb077_alpha_dummy_136 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_136] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_366 (F : Class) (I : Class) : (nb077_alpha_dummy_179 F I) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_179] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_367 (x : Var) : (nb077_alpha_dummy_180 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_180] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_368 (F : Class) (I : Class) : (nb077_alpha_dummy_215 F I) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_215] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_369 (x : Var) : (nb077_alpha_dummy_216 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_216] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_370 (F : Class) (I : Class) : (nb077_alpha_dummy_251 F I) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_251] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_371 (x : Var) : (nb077_alpha_dummy_252 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_252] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_372 (F : Class) (I : Class) : (nb077_alpha_dummy_291 F I) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_291] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_373 (x : Var) : (nb077_alpha_dummy_292 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_292] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_374 (F : Class) (I : Class) : (nb077_alpha_dummy_343 F I) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_343] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_375 (x : Var) : (nb077_alpha_dummy_344 x) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb077_alpha_dummy_344] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb077_fresh_376 (F : Class) (I : Class) : (nb077_alpha_dummy_013 F I) ∉ (((syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) := by
  simpa only [nb077_alpha_dummy_013] using freshVar_not_mem (((syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 0

theorem nb077_fresh_377 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_014 x F I) ∉ (((syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_014] using freshVar_not_mem (((syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 0

theorem nb077_fresh_378 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∉ (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) := by
  simpa only [nb077_alpha_dummy_139] using freshVar_not_mem (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 0

theorem nb077_fresh_379 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∉ (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) := by
  simpa only [nb077_alpha_dummy_140] using freshVar_not_mem (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 1

theorem nb077_fresh_380 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∉ (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) := by
  simpa only [nb077_alpha_dummy_141] using freshVar_not_mem (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 2

theorem nb077_distinct_381 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_140 F I) := by
  simpa only [nb077_alpha_dummy_139, nb077_alpha_dummy_140] using
    (freshVar_injective (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_382 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_141 F I) := by
  simpa only [nb077_alpha_dummy_139, nb077_alpha_dummy_141] using
    (freshVar_injective (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_383 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ≠ (nb077_alpha_dummy_141 F I) := by
  simpa only [nb077_alpha_dummy_140, nb077_alpha_dummy_141] using
    (freshVar_injective (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_384 (x : Var) : (nb077_alpha_dummy_142 x) ∉ (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) := by
  simpa only [nb077_alpha_dummy_142] using freshVar_not_mem (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 0

theorem nb077_fresh_385 (x : Var) : (nb077_alpha_dummy_143 x) ∉ (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) := by
  simpa only [nb077_alpha_dummy_143] using freshVar_not_mem (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 1

theorem nb077_fresh_386 (x : Var) : (nb077_alpha_dummy_144 x) ∉ (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) := by
  simpa only [nb077_alpha_dummy_144] using freshVar_not_mem (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) 2

theorem nb077_distinct_387 (x : Var) : (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_143 x) := by
  simpa only [nb077_alpha_dummy_142, nb077_alpha_dummy_143] using
    (freshVar_injective (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_388 (x : Var) : (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_144 x) := by
  simpa only [nb077_alpha_dummy_142, nb077_alpha_dummy_144] using
    (freshVar_injective (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_389 (x : Var) : (nb077_alpha_dummy_143 x) ≠ (nb077_alpha_dummy_144 x) := by
  simpa only [nb077_alpha_dummy_143, nb077_alpha_dummy_144] using
    (freshVar_injective (((syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_390 (F : Class) (I : Class) : (nb077_alpha_dummy_039 F I) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I)) (Class.cv (nb077_alpha_dummy_035 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I)) (Class.cv (nb077_alpha_dummy_035 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_039] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I)) (Class.cv (nb077_alpha_dummy_035 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I)) (Class.cv (nb077_alpha_dummy_035 F I)))).fv) 0

theorem nb077_fresh_391 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_040 x F I) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I)) (Class.cv (nb077_alpha_dummy_038 x F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I)) (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) := by
  simpa only [nb077_alpha_dummy_040] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I)) (Class.cv (nb077_alpha_dummy_038 x F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I)) (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) 0

theorem nb077_fresh_392 (F : Class) (I : Class) : (nb077_alpha_dummy_087 F I) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I)) (Class.cv (nb077_alpha_dummy_083 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I)) (Class.cv (nb077_alpha_dummy_083 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_087] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I)) (Class.cv (nb077_alpha_dummy_083 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_082 F I)) (Class.cv (nb077_alpha_dummy_083 F I)))).fv) 0

theorem nb077_fresh_393 (x : Var) : (nb077_alpha_dummy_088 x) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv) := by
  simpa only [nb077_alpha_dummy_088] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_085 x)) (Class.cv (nb077_alpha_dummy_086 x)))).fv) 0

theorem nb077_fresh_394 (F : Class) (I : Class) : (nb077_alpha_dummy_123 F I) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I)) (Class.cv (nb077_alpha_dummy_119 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I)) (Class.cv (nb077_alpha_dummy_119 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_123] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I)) (Class.cv (nb077_alpha_dummy_119 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_118 F I)) (Class.cv (nb077_alpha_dummy_119 F I)))).fv) 0

theorem nb077_fresh_395 (x : Var) : (nb077_alpha_dummy_124 x) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv) := by
  simpa only [nb077_alpha_dummy_124] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_121 x)) (Class.cv (nb077_alpha_dummy_122 x)))).fv) 0

theorem nb077_fresh_396 (F : Class) (I : Class) : (nb077_alpha_dummy_167 F I) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I)) (Class.cv (nb077_alpha_dummy_163 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I)) (Class.cv (nb077_alpha_dummy_163 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_167] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I)) (Class.cv (nb077_alpha_dummy_163 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_162 F I)) (Class.cv (nb077_alpha_dummy_163 F I)))).fv) 0

theorem nb077_fresh_397 (x : Var) : (nb077_alpha_dummy_168 x) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv) := by
  simpa only [nb077_alpha_dummy_168] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_165 x)) (Class.cv (nb077_alpha_dummy_166 x)))).fv) 0

theorem nb077_fresh_398 (F : Class) (I : Class) : (nb077_alpha_dummy_203 F I) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I)) (Class.cv (nb077_alpha_dummy_199 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I)) (Class.cv (nb077_alpha_dummy_199 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_203] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I)) (Class.cv (nb077_alpha_dummy_199 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_198 F I)) (Class.cv (nb077_alpha_dummy_199 F I)))).fv) 0

theorem nb077_fresh_399 (x : Var) : (nb077_alpha_dummy_204 x) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv) := by
  simpa only [nb077_alpha_dummy_204] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_201 x)) (Class.cv (nb077_alpha_dummy_202 x)))).fv) 0

theorem nb077_fresh_400 (F : Class) (I : Class) : (nb077_alpha_dummy_239 F I) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I)) (Class.cv (nb077_alpha_dummy_235 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I)) (Class.cv (nb077_alpha_dummy_235 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_239] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I)) (Class.cv (nb077_alpha_dummy_235 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_234 F I)) (Class.cv (nb077_alpha_dummy_235 F I)))).fv) 0

theorem nb077_fresh_401 (x : Var) : (nb077_alpha_dummy_240 x) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv) := by
  simpa only [nb077_alpha_dummy_240] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_237 x)) (Class.cv (nb077_alpha_dummy_238 x)))).fv) 0

theorem nb077_fresh_402 (F : Class) (I : Class) : (nb077_alpha_dummy_279 F I) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I)) (Class.cv (nb077_alpha_dummy_275 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I)) (Class.cv (nb077_alpha_dummy_275 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_279] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I)) (Class.cv (nb077_alpha_dummy_275 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_274 F I)) (Class.cv (nb077_alpha_dummy_275 F I)))).fv) 0

theorem nb077_fresh_403 (x : Var) : (nb077_alpha_dummy_280 x) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv) := by
  simpa only [nb077_alpha_dummy_280] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_277 x)) (Class.cv (nb077_alpha_dummy_278 x)))).fv) 0

theorem nb077_fresh_404 (F : Class) (I : Class) : (nb077_alpha_dummy_301 F I) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I)) (Class.cv (nb077_alpha_dummy_297 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I)) (Class.cv (nb077_alpha_dummy_297 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_301] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I)) (Class.cv (nb077_alpha_dummy_297 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I)) (Class.cv (nb077_alpha_dummy_297 F I)))).fv) 0

theorem nb077_fresh_405 (x : Var) : (nb077_alpha_dummy_302 x) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv) := by
  simpa only [nb077_alpha_dummy_302] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv) 0

theorem nb077_fresh_406 (F : Class) (I : Class) : (nb077_alpha_dummy_331 F I) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I)) (Class.cv (nb077_alpha_dummy_327 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I)) (Class.cv (nb077_alpha_dummy_327 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_331] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I)) (Class.cv (nb077_alpha_dummy_327 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I)) (Class.cv (nb077_alpha_dummy_327 F I)))).fv) 0

theorem nb077_fresh_407 (x : Var) : (nb077_alpha_dummy_332 x) ∉ (((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv) := by
  simpa only [nb077_alpha_dummy_332] using freshVar_not_mem (((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv) 0

theorem nb077_fresh_408 (F : Class) (I : Class) : (nb077_alpha_dummy_055 F I) ∉ (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv) := by
  simpa only [nb077_alpha_dummy_055] using freshVar_not_mem (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv) 0

theorem nb077_fresh_409 (x : Var) (F : Class) : (nb077_alpha_dummy_056 x F) ∉ (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv) := by
  simpa only [nb077_alpha_dummy_056] using freshVar_not_mem (((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st))) (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom F (syn_c2nd))))).fv) 0

theorem nb077_fresh_410 (F : Class) (I : Class) : (nb077_alpha_dummy_011 F I) ∉ (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_011] using freshVar_not_mem (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).fv) 0

theorem nb077_fresh_411 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_012 x F I) ∉ (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) := by
  simpa only [nb077_alpha_dummy_012] using freshVar_not_mem (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) 0

theorem nb077_fresh_412 (F : Class) (I : Class) : (nb077_alpha_dummy_007 F I) ∉ (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_007] using freshVar_not_mem (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv) 0

theorem nb077_fresh_413 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_008 x F I) ∉ (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) := by
  simpa only [nb077_alpha_dummy_008] using freshVar_not_mem (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) 0

theorem nb077_fresh_414 (F : Class) (I : Class) : (nb077_alpha_dummy_053 F I) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_053] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))).fv) 0

theorem nb077_fresh_415 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_054 x F I) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv) := by
  simpa only [nb077_alpha_dummy_054] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))).fv) 0

theorem nb077_fresh_416 (F : Class) (I : Class) : (nb077_alpha_dummy_101 F I) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_101] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_068 F I)))).fv) 0

theorem nb077_fresh_417 (x : Var) : (nb077_alpha_dummy_102 x) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv) := by
  simpa only [nb077_alpha_dummy_102] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_070 x)))).fv) 0

theorem nb077_fresh_418 (F : Class) (I : Class) : (nb077_alpha_dummy_137 F I) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_137] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))).fv) 0

theorem nb077_fresh_419 (x : Var) : (nb077_alpha_dummy_138 x) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv) := by
  simpa only [nb077_alpha_dummy_138] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))).fv) 0

theorem nb077_fresh_420 (F : Class) (I : Class) : (nb077_alpha_dummy_181 F I) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_181] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))).fv) 0

theorem nb077_fresh_421 (x : Var) : (nb077_alpha_dummy_182 x) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv) := by
  simpa only [nb077_alpha_dummy_182] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))).fv) 0

theorem nb077_fresh_422 (F : Class) (I : Class) : (nb077_alpha_dummy_217 F I) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_217] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_184 F I)))).fv) 0

theorem nb077_fresh_423 (x : Var) : (nb077_alpha_dummy_218 x) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv) := by
  simpa only [nb077_alpha_dummy_218] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_186 x)))).fv) 0

theorem nb077_fresh_424 (F : Class) (I : Class) : (nb077_alpha_dummy_253 F I) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_253] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_220 F I)))).fv) 0

theorem nb077_fresh_425 (x : Var) : (nb077_alpha_dummy_254 x) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv) := by
  simpa only [nb077_alpha_dummy_254] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_222 x)))).fv) 0

theorem nb077_fresh_426 (F : Class) (I : Class) : (nb077_alpha_dummy_293 F I) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_293] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_260 F I)))).fv) 0

theorem nb077_fresh_427 (x : Var) : (nb077_alpha_dummy_294 x) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv) := by
  simpa only [nb077_alpha_dummy_294] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_262 x)))).fv) 0

theorem nb077_fresh_428 (F : Class) (I : Class) : (nb077_alpha_dummy_345 F I) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv) := by
  simpa only [nb077_alpha_dummy_345] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv) 0

theorem nb077_fresh_429 (x : Var) : (nb077_alpha_dummy_346 x) ∉ (((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv) := by
  simpa only [nb077_alpha_dummy_346] using freshVar_not_mem (((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv) 0

theorem nb077_fresh_430 (F : Class) (I : Class) : (nb077_alpha_dummy_015 F I) ∉ (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) := by
  simpa only [nb077_alpha_dummy_015] using freshVar_not_mem (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 0

theorem nb077_fresh_431 (F : Class) (I : Class) : (nb077_alpha_dummy_016 F I) ∉ (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) := by
  simpa only [nb077_alpha_dummy_016] using freshVar_not_mem (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 1

theorem nb077_distinct_432 (F : Class) (I : Class) : (nb077_alpha_dummy_015 F I) ≠ (nb077_alpha_dummy_016 F I) := by
  simpa only [nb077_alpha_dummy_015, nb077_alpha_dummy_016] using
    (freshVar_injective (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_433 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_017 x F I) ∉ (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_017] using freshVar_not_mem (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 0

theorem nb077_fresh_434 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_018 x F I) ∉ (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_018] using freshVar_not_mem (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 1

theorem nb077_distinct_435 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_017 x F I) ≠ (nb077_alpha_dummy_018 x F I) := by
  simpa only [nb077_alpha_dummy_017, nb077_alpha_dummy_018] using
    (freshVar_injective (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_436 (F : Class) (I : Class) : (nb077_alpha_dummy_009 F I) ∉ (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) := by
  simpa only [nb077_alpha_dummy_009] using freshVar_not_mem (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 0

theorem nb077_fresh_437 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_010 x F I) ∉ (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_010] using freshVar_not_mem (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 0

theorem nb077_fresh_438 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∉ (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv) := by
  simpa only [nb077_alpha_dummy_001] using freshVar_not_mem (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv) 0

theorem nb077_fresh_439 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∉ (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv) := by
  simpa only [nb077_alpha_dummy_002] using freshVar_not_mem (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv) 0

theorem nb077_fresh_440 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∉ ((F).fv ∪ (I).fv) := by
  simpa only [nb077_alpha_dummy_000] using freshVar_not_mem ((F).fv ∪ (I).fv) 0

theorem nb077_fresh_441 (F : Class) (I : Class) : (nb077_alpha_dummy_255 F I) ∉ (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))).fv) := by
  simpa only [nb077_alpha_dummy_255] using freshVar_not_mem (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))).fv) 0

theorem nb077_fresh_442 (F : Class) (I : Class) : (nb077_alpha_dummy_257 F I) ∉ (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_255 F I)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb077_alpha_dummy_000 F I)) (syn_cvv)) (Wff.classEq (Class.cv (nb077_alpha_dummy_255 F I)) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))))).fv) := by
  simpa only [nb077_alpha_dummy_257] using freshVar_not_mem (({(nb077_alpha_dummy_000 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_255 F I)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb077_alpha_dummy_000 F I)) (syn_cvv)) (Wff.classEq (Class.cv (nb077_alpha_dummy_255 F I)) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))))).fv) 0

theorem nb077_fresh_443 (F : Class) (I : Class) : (nb077_alpha_dummy_065 F I) ∉ (({(nb077_alpha_dummy_059 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_060 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_061 F I) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_059 F I)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)) (Class.cv (nb077_alpha_dummy_061 F I))) (syn_wbr (Class.cv (nb077_alpha_dummy_061 F I)) (syn_ccnv (syn_c1st)) (Class.cv (nb077_alpha_dummy_060 F I)))))).fv) := by
  simpa only [nb077_alpha_dummy_065] using freshVar_not_mem (({(nb077_alpha_dummy_059 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_060 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_061 F I) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_059 F I)) (syn_ccom (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (syn_c1st)) (Class.cv (nb077_alpha_dummy_061 F I))) (syn_wbr (Class.cv (nb077_alpha_dummy_061 F I)) (syn_ccnv (syn_c1st)) (Class.cv (nb077_alpha_dummy_060 F I)))))).fv) 0

theorem nb077_fresh_444 (x : Var) : (nb077_alpha_dummy_066 x) ∉ (({(nb077_alpha_dummy_062 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_063 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_064 x) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_062 x)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)) (Class.cv (nb077_alpha_dummy_064 x))) (syn_wbr (Class.cv (nb077_alpha_dummy_064 x)) (syn_ccnv (syn_c1st)) (Class.cv (nb077_alpha_dummy_063 x)))))).fv) := by
  simpa only [nb077_alpha_dummy_066] using freshVar_not_mem (({(nb077_alpha_dummy_062 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_063 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_064 x) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_062 x)) (syn_ccom (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (syn_c1st)) (Class.cv (nb077_alpha_dummy_064 x))) (syn_wbr (Class.cv (nb077_alpha_dummy_064 x)) (syn_ccnv (syn_c1st)) (Class.cv (nb077_alpha_dummy_063 x)))))).fv) 0

theorem nb077_fresh_445 (F : Class) (I : Class) : (nb077_alpha_dummy_145 F I) ∉ (({(nb077_alpha_dummy_139 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_140 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_141 F I) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_139 F I)) (syn_c1st) (Class.cv (nb077_alpha_dummy_141 F I))) (syn_wbr (Class.cv (nb077_alpha_dummy_141 F I)) (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (Class.cv (nb077_alpha_dummy_140 F I)))))).fv) := by
  simpa only [nb077_alpha_dummy_145] using freshVar_not_mem (({(nb077_alpha_dummy_139 F I)} : Finset Var) ∪ ({(nb077_alpha_dummy_140 F I)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_141 F I) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_139 F I)) (syn_c1st) (Class.cv (nb077_alpha_dummy_141 F I))) (syn_wbr (Class.cv (nb077_alpha_dummy_141 F I)) (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) (Class.cv (nb077_alpha_dummy_140 F I)))))).fv) 0

theorem nb077_fresh_446 (x : Var) : (nb077_alpha_dummy_146 x) ∉ (({(nb077_alpha_dummy_142 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_143 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_144 x) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_142 x)) (syn_c1st) (Class.cv (nb077_alpha_dummy_144 x))) (syn_wbr (Class.cv (nb077_alpha_dummy_144 x)) (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (Class.cv (nb077_alpha_dummy_143 x)))))).fv) := by
  simpa only [nb077_alpha_dummy_146] using freshVar_not_mem (({(nb077_alpha_dummy_142 x)} : Finset Var) ∪ ({(nb077_alpha_dummy_143 x)} : Finset Var) ∪ ((syn_wex (nb077_alpha_dummy_144 x) (syn_wa (syn_wbr (Class.cv (nb077_alpha_dummy_142 x)) (syn_c1st) (Class.cv (nb077_alpha_dummy_144 x))) (syn_wbr (Class.cv (nb077_alpha_dummy_144 x)) (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) (Class.cv (nb077_alpha_dummy_143 x)))))).fv) 0

theorem nb077_fresh_447 (x : Var) : (nb077_alpha_dummy_256 x) ∉ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (syn_c1c))).fv) := by
  simpa only [nb077_alpha_dummy_256] using freshVar_not_mem (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (syn_c1c))).fv) 0

theorem nb077_fresh_448 (x : Var) : (nb077_alpha_dummy_258 x) ∉ (({x} : Finset Var) ∪ ({(nb077_alpha_dummy_256 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb077_alpha_dummy_256 x)) (syn_cplc (Class.cv x) (syn_c1c))))).fv) := by
  simpa only [nb077_alpha_dummy_258] using freshVar_not_mem (({x} : Finset Var) ∪ ({(nb077_alpha_dummy_256 x)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classEq (Class.cv (nb077_alpha_dummy_256 x)) (syn_cplc (Class.cv x) (syn_c1c))))).fv) 0

theorem nb077_support_mem_0000 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∈ (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0001 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∈ (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0002 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∈ (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0003 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∈ (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0004 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∈ (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_cima]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0005 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∈ (((syn_cnin (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_cima]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0006 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∈ (((syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cima]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0007 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∈ (((syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cima]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0008 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∈ (((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0009 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∈ (((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0010 (F : Class) (I : Class) : (nb077_alpha_dummy_016 F I) ∈ (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_015 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0011 (F : Class) (I : Class) : (nb077_alpha_dummy_016 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0012 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_018 x F I) ∈ (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0013 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_018 x F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0014 (F : Class) (I : Class) : (nb077_alpha_dummy_016 F I) ∈ (((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0010 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0015 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_018 x F I) ∈ (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0016 (F : Class) (I : Class) : (nb077_alpha_dummy_020 F I) ∈ (((Class.cv (nb077_alpha_dummy_020 F I))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0017 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_022 x F I) ∈ (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0018 (F : Class) (I : Class) : (nb077_alpha_dummy_027 F I) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_027 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_027 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_027 F I))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0019 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_029 x F I) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_029 x F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_029 x F I))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0020 (F : Class) (I : Class) : (nb077_alpha_dummy_027 F I) ∈ (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0021 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_029 x F I) ∈ (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0022 (F : Class) (I : Class) : (nb077_alpha_dummy_034 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I)) (Class.cv (nb077_alpha_dummy_035 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I)) (Class.cv (nb077_alpha_dummy_035 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0023 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_037 x F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I)) (Class.cv (nb077_alpha_dummy_038 x F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I)) (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0024 (F : Class) (I : Class) : (nb077_alpha_dummy_034 F I) ∈ (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_035 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0025 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_037 x F I) ∈ (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0026 (F : Class) (I : Class) : (nb077_alpha_dummy_035 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I)) (Class.cv (nb077_alpha_dummy_035 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_034 F I)) (Class.cv (nb077_alpha_dummy_035 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0027 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_038 x F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I)) (Class.cv (nb077_alpha_dummy_038 x F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_037 x F I)) (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0028 (F : Class) (I : Class) : (nb077_alpha_dummy_035 F I) ∈ (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_035 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0029 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_038 x F I) ∈ (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0030 (F : Class) (I : Class) : (nb077_alpha_dummy_034 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_034 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_035 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0031 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_037 x F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_037 x F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0032 (F : Class) (I : Class) : (nb077_alpha_dummy_034 F I) ∈ (((Class.cv (nb077_alpha_dummy_034 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_034 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0033 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_037 x F I) ∈ (((Class.cv (nb077_alpha_dummy_037 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_037 x F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0034 (F : Class) (I : Class) : (nb077_alpha_dummy_035 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_034 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_035 F I)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0035 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_038 x F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_037 x F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_038 x F I)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0036 (F : Class) (I : Class) : (nb077_alpha_dummy_035 F I) ∈ (((Class.cv (nb077_alpha_dummy_035 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_035 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0037 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_038 x F I) ∈ (((Class.cv (nb077_alpha_dummy_038 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_038 x F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0038 (F : Class) (I : Class) : (nb077_alpha_dummy_015 F I) ∈ (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_015 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
