import NAR4C078C001Part012

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

theorem nb078_distinct_404 : (nb078_alpha_dummy_1185) ≠ (nb078_alpha_dummy_1187) := by
  simpa only [nb078_alpha_dummy_1185, nb078_alpha_dummy_1187] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_405 : (nb078_alpha_dummy_1186) ≠ (nb078_alpha_dummy_1187) := by
  simpa only [nb078_alpha_dummy_1186, nb078_alpha_dummy_1187] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_406 (h : Var) : (nb078_alpha_dummy_1188 h) ∉ (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1188] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_407 (h : Var) : (nb078_alpha_dummy_1189 h) ∉ (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1189] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_408 (h : Var) : (nb078_alpha_dummy_1190 h) ∉ (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1190] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_409 (h : Var) : (nb078_alpha_dummy_1188 h) ≠ (nb078_alpha_dummy_1189 h) := by
  simpa only [nb078_alpha_dummy_1188, nb078_alpha_dummy_1189] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_410 (h : Var) : (nb078_alpha_dummy_1188 h) ≠ (nb078_alpha_dummy_1190 h) := by
  simpa only [nb078_alpha_dummy_1188, nb078_alpha_dummy_1190] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_411 (h : Var) : (nb078_alpha_dummy_1189 h) ≠ (nb078_alpha_dummy_1190 h) := by
  simpa only [nb078_alpha_dummy_1189, nb078_alpha_dummy_1190] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_412 : (nb078_alpha_dummy_1197) ∉ (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1186))).fv) := by
  simpa only [nb078_alpha_dummy_1197] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1186))).fv) 0

theorem nb078_fresh_413 : (nb078_alpha_dummy_1193) ∉ (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) := by
  simpa only [nb078_alpha_dummy_1193] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) 0

theorem nb078_fresh_414 : (nb078_alpha_dummy_1199) ∉ (((Class.cv (nb078_alpha_dummy_1187))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) := by
  simpa only [nb078_alpha_dummy_1199] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1187))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) 0

theorem nb078_fresh_415 (h : Var) : (nb078_alpha_dummy_1198 h) ∉ (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1189 h))).fv) := by
  simpa only [nb078_alpha_dummy_1198] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1189 h))).fv) 0

theorem nb078_fresh_416 (h : Var) : (nb078_alpha_dummy_1194 h) ∉ (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1190 h))).fv) := by
  simpa only [nb078_alpha_dummy_1194] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1190 h))).fv) 0

theorem nb078_fresh_417 (h : Var) : (nb078_alpha_dummy_1200 h) ∉ (((Class.cv (nb078_alpha_dummy_1190 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1190 h))).fv) := by
  simpa only [nb078_alpha_dummy_1200] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1190 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1190 h))).fv) 0

theorem nb078_fresh_418 : (nb078_alpha_dummy_1215) ∉ (((Class.cv (nb078_alpha_dummy_1208))).fv) := by
  simpa only [nb078_alpha_dummy_1215] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1208))).fv) 0

theorem nb078_fresh_419 : (nb078_alpha_dummy_1216) ∉ (((Class.cv (nb078_alpha_dummy_1208))).fv) := by
  simpa only [nb078_alpha_dummy_1216] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1208))).fv) 1

theorem nb078_distinct_420 : (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1216) := by
  simpa only [nb078_alpha_dummy_1215, nb078_alpha_dummy_1216] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1208))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_421 (h : Var) : (nb078_alpha_dummy_1217 h) ∉ (((Class.cv (nb078_alpha_dummy_1210 h))).fv) := by
  simpa only [nb078_alpha_dummy_1217] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1210 h))).fv) 0

theorem nb078_fresh_422 (h : Var) : (nb078_alpha_dummy_1218 h) ∉ (((Class.cv (nb078_alpha_dummy_1210 h))).fv) := by
  simpa only [nb078_alpha_dummy_1218] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1210 h))).fv) 1

theorem nb078_distinct_423 (h : Var) : (nb078_alpha_dummy_1217 h) ≠ (nb078_alpha_dummy_1218 h) := by
  simpa only [nb078_alpha_dummy_1217, nb078_alpha_dummy_1218] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1210 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_424 : (nb078_alpha_dummy_1221) ∉ (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1221] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_425 : (nb078_alpha_dummy_1222) ∉ (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1222] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_426 : (nb078_alpha_dummy_1223) ∉ (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1223] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_427 : (nb078_alpha_dummy_1221) ≠ (nb078_alpha_dummy_1222) := by
  simpa only [nb078_alpha_dummy_1221, nb078_alpha_dummy_1222] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_428 : (nb078_alpha_dummy_1221) ≠ (nb078_alpha_dummy_1223) := by
  simpa only [nb078_alpha_dummy_1221, nb078_alpha_dummy_1223] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_429 : (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1223) := by
  simpa only [nb078_alpha_dummy_1222, nb078_alpha_dummy_1223] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_430 (h : Var) : (nb078_alpha_dummy_1224 h) ∉ (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1224] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_431 (h : Var) : (nb078_alpha_dummy_1225 h) ∉ (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1225] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_432 (h : Var) : (nb078_alpha_dummy_1226 h) ∉ (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1226] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_433 (h : Var) : (nb078_alpha_dummy_1224 h) ≠ (nb078_alpha_dummy_1225 h) := by
  simpa only [nb078_alpha_dummy_1224, nb078_alpha_dummy_1225] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_434 (h : Var) : (nb078_alpha_dummy_1224 h) ≠ (nb078_alpha_dummy_1226 h) := by
  simpa only [nb078_alpha_dummy_1224, nb078_alpha_dummy_1226] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_435 (h : Var) : (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1226 h) := by
  simpa only [nb078_alpha_dummy_1225, nb078_alpha_dummy_1226] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_436 : (nb078_alpha_dummy_1233) ∉ (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1222))).fv) := by
  simpa only [nb078_alpha_dummy_1233] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1222))).fv) 0

theorem nb078_fresh_437 : (nb078_alpha_dummy_1229) ∉ (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) := by
  simpa only [nb078_alpha_dummy_1229] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) 0

theorem nb078_fresh_438 : (nb078_alpha_dummy_1235) ∉ (((Class.cv (nb078_alpha_dummy_1223))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) := by
  simpa only [nb078_alpha_dummy_1235] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1223))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) 0

theorem nb078_fresh_439 (h : Var) : (nb078_alpha_dummy_1234 h) ∉ (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1225 h))).fv) := by
  simpa only [nb078_alpha_dummy_1234] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1225 h))).fv) 0

theorem nb078_fresh_440 (h : Var) : (nb078_alpha_dummy_1230 h) ∉ (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1226 h))).fv) := by
  simpa only [nb078_alpha_dummy_1230] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1226 h))).fv) 0

theorem nb078_fresh_441 (h : Var) : (nb078_alpha_dummy_1236 h) ∉ (((Class.cv (nb078_alpha_dummy_1226 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1226 h))).fv) := by
  simpa only [nb078_alpha_dummy_1236] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1226 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1226 h))).fv) 0

theorem nb078_fresh_442 : (nb078_alpha_dummy_139) ∉ (((Class.cv (nb078_alpha_dummy_132))).fv) := by
  simpa only [nb078_alpha_dummy_139] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_132))).fv) 0

theorem nb078_fresh_443 : (nb078_alpha_dummy_140) ∉ (((Class.cv (nb078_alpha_dummy_132))).fv) := by
  simpa only [nb078_alpha_dummy_140] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_132))).fv) 1

theorem nb078_distinct_444 : (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_140) := by
  simpa only [nb078_alpha_dummy_139, nb078_alpha_dummy_140] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_132))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_445 (f : Var) : (nb078_alpha_dummy_141 f) ∉ (((Class.cv (nb078_alpha_dummy_134 f))).fv) := by
  simpa only [nb078_alpha_dummy_141] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_134 f))).fv) 0

theorem nb078_fresh_446 (f : Var) : (nb078_alpha_dummy_142 f) ∉ (((Class.cv (nb078_alpha_dummy_134 f))).fv) := by
  simpa only [nb078_alpha_dummy_142] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_134 f))).fv) 1

theorem nb078_distinct_447 (f : Var) : (nb078_alpha_dummy_141 f) ≠ (nb078_alpha_dummy_142 f) := by
  simpa only [nb078_alpha_dummy_141, nb078_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_134 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_448 : (nb078_alpha_dummy_145) ∉ (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_145] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_449 : (nb078_alpha_dummy_146) ∉ (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_146] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_450 : (nb078_alpha_dummy_147) ∉ (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_147] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_451 : (nb078_alpha_dummy_145) ≠ (nb078_alpha_dummy_146) := by
  simpa only [nb078_alpha_dummy_145, nb078_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_452 : (nb078_alpha_dummy_145) ≠ (nb078_alpha_dummy_147) := by
  simpa only [nb078_alpha_dummy_145, nb078_alpha_dummy_147] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_453 : (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_147) := by
  simpa only [nb078_alpha_dummy_146, nb078_alpha_dummy_147] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_454 (f : Var) : (nb078_alpha_dummy_148 f) ∉ (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_148] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_455 (f : Var) : (nb078_alpha_dummy_149 f) ∉ (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_149] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_456 (f : Var) : (nb078_alpha_dummy_150 f) ∉ (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_150] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_457 (f : Var) : (nb078_alpha_dummy_148 f) ≠ (nb078_alpha_dummy_149 f) := by
  simpa only [nb078_alpha_dummy_148, nb078_alpha_dummy_149] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_458 (f : Var) : (nb078_alpha_dummy_148 f) ≠ (nb078_alpha_dummy_150 f) := by
  simpa only [nb078_alpha_dummy_148, nb078_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_459 (f : Var) : (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_150 f) := by
  simpa only [nb078_alpha_dummy_149, nb078_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_460 : (nb078_alpha_dummy_157) ∉ (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_146))).fv) := by
  simpa only [nb078_alpha_dummy_157] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_146))).fv) 0

theorem nb078_fresh_461 : (nb078_alpha_dummy_153) ∉ (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) := by
  simpa only [nb078_alpha_dummy_153] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) 0

theorem nb078_fresh_462 : (nb078_alpha_dummy_159) ∉ (((Class.cv (nb078_alpha_dummy_147))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) := by
  simpa only [nb078_alpha_dummy_159] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_147))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) 0

theorem nb078_fresh_463 (f : Var) : (nb078_alpha_dummy_158 f) ∉ (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_149 f))).fv) := by
  simpa only [nb078_alpha_dummy_158] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_149 f))).fv) 0

theorem nb078_fresh_464 (f : Var) : (nb078_alpha_dummy_154 f) ∉ (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) := by
  simpa only [nb078_alpha_dummy_154] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) 0

theorem nb078_fresh_465 (f : Var) : (nb078_alpha_dummy_160 f) ∉ (((Class.cv (nb078_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) := by
  simpa only [nb078_alpha_dummy_160] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) 0

theorem nb078_fresh_466 : (nb078_alpha_dummy_175) ∉ (((Class.cv (nb078_alpha_dummy_168))).fv) := by
  simpa only [nb078_alpha_dummy_175] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_168))).fv) 0

theorem nb078_fresh_467 : (nb078_alpha_dummy_176) ∉ (((Class.cv (nb078_alpha_dummy_168))).fv) := by
  simpa only [nb078_alpha_dummy_176] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_168))).fv) 1

theorem nb078_distinct_468 : (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_176) := by
  simpa only [nb078_alpha_dummy_175, nb078_alpha_dummy_176] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_168))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_469 (f : Var) : (nb078_alpha_dummy_177 f) ∉ (((Class.cv (nb078_alpha_dummy_170 f))).fv) := by
  simpa only [nb078_alpha_dummy_177] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_170 f))).fv) 0

theorem nb078_fresh_470 (f : Var) : (nb078_alpha_dummy_178 f) ∉ (((Class.cv (nb078_alpha_dummy_170 f))).fv) := by
  simpa only [nb078_alpha_dummy_178] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_170 f))).fv) 1

theorem nb078_distinct_471 (f : Var) : (nb078_alpha_dummy_177 f) ≠ (nb078_alpha_dummy_178 f) := by
  simpa only [nb078_alpha_dummy_177, nb078_alpha_dummy_178] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_170 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_472 : (nb078_alpha_dummy_181) ∉ (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_181] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_473 : (nb078_alpha_dummy_182) ∉ (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_182] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_474 : (nb078_alpha_dummy_183) ∉ (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_183] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_475 : (nb078_alpha_dummy_181) ≠ (nb078_alpha_dummy_182) := by
  simpa only [nb078_alpha_dummy_181, nb078_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_476 : (nb078_alpha_dummy_181) ≠ (nb078_alpha_dummy_183) := by
  simpa only [nb078_alpha_dummy_181, nb078_alpha_dummy_183] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_477 : (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_183) := by
  simpa only [nb078_alpha_dummy_182, nb078_alpha_dummy_183] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_478 (f : Var) : (nb078_alpha_dummy_184 f) ∉ (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_184] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_479 (f : Var) : (nb078_alpha_dummy_185 f) ∉ (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_185] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_480 (f : Var) : (nb078_alpha_dummy_186 f) ∉ (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_186] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_481 (f : Var) : (nb078_alpha_dummy_184 f) ≠ (nb078_alpha_dummy_185 f) := by
  simpa only [nb078_alpha_dummy_184, nb078_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_482 (f : Var) : (nb078_alpha_dummy_184 f) ≠ (nb078_alpha_dummy_186 f) := by
  simpa only [nb078_alpha_dummy_184, nb078_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_483 (f : Var) : (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_186 f) := by
  simpa only [nb078_alpha_dummy_185, nb078_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_484 : (nb078_alpha_dummy_193) ∉ (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_182))).fv) := by
  simpa only [nb078_alpha_dummy_193] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_182))).fv) 0

theorem nb078_fresh_485 : (nb078_alpha_dummy_189) ∉ (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) := by
  simpa only [nb078_alpha_dummy_189] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) 0

theorem nb078_fresh_486 : (nb078_alpha_dummy_195) ∉ (((Class.cv (nb078_alpha_dummy_183))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) := by
  simpa only [nb078_alpha_dummy_195] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_183))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) 0

theorem nb078_fresh_487 (f : Var) : (nb078_alpha_dummy_194 f) ∉ (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_185 f))).fv) := by
  simpa only [nb078_alpha_dummy_194] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_185 f))).fv) 0

theorem nb078_fresh_488 (f : Var) : (nb078_alpha_dummy_190 f) ∉ (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) := by
  simpa only [nb078_alpha_dummy_190] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) 0

theorem nb078_fresh_489 (f : Var) : (nb078_alpha_dummy_196 f) ∉ (((Class.cv (nb078_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) := by
  simpa only [nb078_alpha_dummy_196] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) 0

theorem nb078_fresh_490 : (nb078_alpha_dummy_207) ∉ (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) := by
  simpa only [nb078_alpha_dummy_207] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) 0

theorem nb078_fresh_491 : (nb078_alpha_dummy_208) ∉ (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) := by
  simpa only [nb078_alpha_dummy_208] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) 1

theorem nb078_distinct_492 : (nb078_alpha_dummy_207) ≠ (nb078_alpha_dummy_208) := by
  simpa only [nb078_alpha_dummy_207, nb078_alpha_dummy_208] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_493 (f : Var) : (nb078_alpha_dummy_209 f) ∉ (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) := by
  simpa only [nb078_alpha_dummy_209] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) 0

theorem nb078_fresh_494 (f : Var) : (nb078_alpha_dummy_210 f) ∉ (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) := by
  simpa only [nb078_alpha_dummy_210] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) 1

theorem nb078_distinct_495 (f : Var) : (nb078_alpha_dummy_209 f) ≠ (nb078_alpha_dummy_210 f) := by
  simpa only [nb078_alpha_dummy_209, nb078_alpha_dummy_210] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_496 : (nb078_alpha_dummy_215) ∉ (((Class.cv (nb078_alpha_dummy_208))).fv) := by
  simpa only [nb078_alpha_dummy_215] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_208))).fv) 0

theorem nb078_fresh_497 : (nb078_alpha_dummy_216) ∉ (((Class.cv (nb078_alpha_dummy_208))).fv) := by
  simpa only [nb078_alpha_dummy_216] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_208))).fv) 1

theorem nb078_distinct_498 : (nb078_alpha_dummy_215) ≠ (nb078_alpha_dummy_216) := by
  simpa only [nb078_alpha_dummy_215, nb078_alpha_dummy_216] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_208))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_499 (f : Var) : (nb078_alpha_dummy_217 f) ∉ (((Class.cv (nb078_alpha_dummy_210 f))).fv) := by
  simpa only [nb078_alpha_dummy_217] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_210 f))).fv) 0

theorem nb078_fresh_500 (f : Var) : (nb078_alpha_dummy_218 f) ∉ (((Class.cv (nb078_alpha_dummy_210 f))).fv) := by
  simpa only [nb078_alpha_dummy_218] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_210 f))).fv) 1

theorem nb078_distinct_501 (f : Var) : (nb078_alpha_dummy_217 f) ≠ (nb078_alpha_dummy_218 f) := by
  simpa only [nb078_alpha_dummy_217, nb078_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_210 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_502 : (nb078_alpha_dummy_221) ∉ (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_221] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_503 : (nb078_alpha_dummy_222) ∉ (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_222] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_504 : (nb078_alpha_dummy_223) ∉ (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_223] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_505 : (nb078_alpha_dummy_221) ≠ (nb078_alpha_dummy_222) := by
  simpa only [nb078_alpha_dummy_221, nb078_alpha_dummy_222] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_506 : (nb078_alpha_dummy_221) ≠ (nb078_alpha_dummy_223) := by
  simpa only [nb078_alpha_dummy_221, nb078_alpha_dummy_223] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_507 : (nb078_alpha_dummy_222) ≠ (nb078_alpha_dummy_223) := by
  simpa only [nb078_alpha_dummy_222, nb078_alpha_dummy_223] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_508 (f : Var) : (nb078_alpha_dummy_224 f) ∉ (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_224] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_509 (f : Var) : (nb078_alpha_dummy_225 f) ∉ (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_225] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_510 (f : Var) : (nb078_alpha_dummy_226 f) ∉ (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_226] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_511 (f : Var) : (nb078_alpha_dummy_224 f) ≠ (nb078_alpha_dummy_225 f) := by
  simpa only [nb078_alpha_dummy_224, nb078_alpha_dummy_225] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_512 (f : Var) : (nb078_alpha_dummy_224 f) ≠ (nb078_alpha_dummy_226 f) := by
  simpa only [nb078_alpha_dummy_224, nb078_alpha_dummy_226] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_513 (f : Var) : (nb078_alpha_dummy_225 f) ≠ (nb078_alpha_dummy_226 f) := by
  simpa only [nb078_alpha_dummy_225, nb078_alpha_dummy_226] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_514 : (nb078_alpha_dummy_233) ∉ (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_222))).fv) := by
  simpa only [nb078_alpha_dummy_233] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_222))).fv) 0

theorem nb078_fresh_515 : (nb078_alpha_dummy_229) ∉ (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) := by
  simpa only [nb078_alpha_dummy_229] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) 0

theorem nb078_fresh_516 : (nb078_alpha_dummy_235) ∉ (((Class.cv (nb078_alpha_dummy_223))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) := by
  simpa only [nb078_alpha_dummy_235] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_223))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) 0

theorem nb078_fresh_517 (f : Var) : (nb078_alpha_dummy_234 f) ∉ (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_225 f))).fv) := by
  simpa only [nb078_alpha_dummy_234] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_225 f))).fv) 0

theorem nb078_fresh_518 (f : Var) : (nb078_alpha_dummy_230 f) ∉ (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) := by
  simpa only [nb078_alpha_dummy_230] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) 0

theorem nb078_fresh_519 (f : Var) : (nb078_alpha_dummy_236 f) ∉ (((Class.cv (nb078_alpha_dummy_226 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) := by
  simpa only [nb078_alpha_dummy_236] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_226 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) 0

theorem nb078_fresh_520 : (nb078_alpha_dummy_247) ∉ (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) := by
  simpa only [nb078_alpha_dummy_247] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) 0

theorem nb078_fresh_521 : (nb078_alpha_dummy_248) ∉ (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) := by
  simpa only [nb078_alpha_dummy_248] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) 1

theorem nb078_distinct_522 : (nb078_alpha_dummy_247) ≠ (nb078_alpha_dummy_248) := by
  simpa only [nb078_alpha_dummy_247, nb078_alpha_dummy_248] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_523 (f : Var) : (nb078_alpha_dummy_249 f) ∉ (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) := by
  simpa only [nb078_alpha_dummy_249] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) 0

theorem nb078_fresh_524 (f : Var) : (nb078_alpha_dummy_250 f) ∉ (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) := by
  simpa only [nb078_alpha_dummy_250] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) 1

theorem nb078_distinct_525 (f : Var) : (nb078_alpha_dummy_249 f) ≠ (nb078_alpha_dummy_250 f) := by
  simpa only [nb078_alpha_dummy_249, nb078_alpha_dummy_250] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_526 : (nb078_alpha_dummy_255) ∉ (((Class.cv (nb078_alpha_dummy_248))).fv) := by
  simpa only [nb078_alpha_dummy_255] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_248))).fv) 0

theorem nb078_fresh_527 : (nb078_alpha_dummy_256) ∉ (((Class.cv (nb078_alpha_dummy_248))).fv) := by
  simpa only [nb078_alpha_dummy_256] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_248))).fv) 1

theorem nb078_distinct_528 : (nb078_alpha_dummy_255) ≠ (nb078_alpha_dummy_256) := by
  simpa only [nb078_alpha_dummy_255, nb078_alpha_dummy_256] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_248))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_529 (f : Var) : (nb078_alpha_dummy_257 f) ∉ (((Class.cv (nb078_alpha_dummy_250 f))).fv) := by
  simpa only [nb078_alpha_dummy_257] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_250 f))).fv) 0

theorem nb078_fresh_530 (f : Var) : (nb078_alpha_dummy_258 f) ∉ (((Class.cv (nb078_alpha_dummy_250 f))).fv) := by
  simpa only [nb078_alpha_dummy_258] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_250 f))).fv) 1

theorem nb078_distinct_531 (f : Var) : (nb078_alpha_dummy_257 f) ≠ (nb078_alpha_dummy_258 f) := by
  simpa only [nb078_alpha_dummy_257, nb078_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_250 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_532 : (nb078_alpha_dummy_261) ∉ (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_261] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_533 : (nb078_alpha_dummy_262) ∉ (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_262] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_534 : (nb078_alpha_dummy_263) ∉ (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_263] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_535 : (nb078_alpha_dummy_261) ≠ (nb078_alpha_dummy_262) := by
  simpa only [nb078_alpha_dummy_261, nb078_alpha_dummy_262] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_536 : (nb078_alpha_dummy_261) ≠ (nb078_alpha_dummy_263) := by
  simpa only [nb078_alpha_dummy_261, nb078_alpha_dummy_263] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_537 : (nb078_alpha_dummy_262) ≠ (nb078_alpha_dummy_263) := by
  simpa only [nb078_alpha_dummy_262, nb078_alpha_dummy_263] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_538 (f : Var) : (nb078_alpha_dummy_264 f) ∉ (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_264] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_539 (f : Var) : (nb078_alpha_dummy_265 f) ∉ (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_265] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_540 (f : Var) : (nb078_alpha_dummy_266 f) ∉ (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_266] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_541 (f : Var) : (nb078_alpha_dummy_264 f) ≠ (nb078_alpha_dummy_265 f) := by
  simpa only [nb078_alpha_dummy_264, nb078_alpha_dummy_265] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_542 (f : Var) : (nb078_alpha_dummy_264 f) ≠ (nb078_alpha_dummy_266 f) := by
  simpa only [nb078_alpha_dummy_264, nb078_alpha_dummy_266] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_543 (f : Var) : (nb078_alpha_dummy_265 f) ≠ (nb078_alpha_dummy_266 f) := by
  simpa only [nb078_alpha_dummy_265, nb078_alpha_dummy_266] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_544 : (nb078_alpha_dummy_273) ∉ (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_262))).fv) := by
  simpa only [nb078_alpha_dummy_273] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_262))).fv) 0

theorem nb078_fresh_545 : (nb078_alpha_dummy_269) ∉ (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) := by
  simpa only [nb078_alpha_dummy_269] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) 0

theorem nb078_fresh_546 : (nb078_alpha_dummy_275) ∉ (((Class.cv (nb078_alpha_dummy_263))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) := by
  simpa only [nb078_alpha_dummy_275] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_263))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) 0

theorem nb078_fresh_547 (f : Var) : (nb078_alpha_dummy_274 f) ∉ (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_265 f))).fv) := by
  simpa only [nb078_alpha_dummy_274] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_265 f))).fv) 0

theorem nb078_fresh_548 (f : Var) : (nb078_alpha_dummy_270 f) ∉ (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) := by
  simpa only [nb078_alpha_dummy_270] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) 0

theorem nb078_fresh_549 (f : Var) : (nb078_alpha_dummy_276 f) ∉ (((Class.cv (nb078_alpha_dummy_266 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) := by
  simpa only [nb078_alpha_dummy_276] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_266 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) 0

theorem nb078_fresh_550 : (nb078_alpha_dummy_295) ∉ (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) := by
  simpa only [nb078_alpha_dummy_295] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 0

theorem nb078_fresh_551 : (nb078_alpha_dummy_296) ∉ (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) := by
  simpa only [nb078_alpha_dummy_296] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) 1

theorem nb078_distinct_552 : (nb078_alpha_dummy_295) ≠ (nb078_alpha_dummy_296) := by
  simpa only [nb078_alpha_dummy_295, nb078_alpha_dummy_296] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_553 : (nb078_alpha_dummy_331) ∉ (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) := by
  simpa only [nb078_alpha_dummy_331] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
