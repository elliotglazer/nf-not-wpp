import NAR4C078C001Part011

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

theorem nb078_fresh_254 (h : Var) : (nb078_alpha_dummy_1020 h) ∉ (((Class.cv (nb078_alpha_dummy_1012 h))).fv) := by
  simpa only [nb078_alpha_dummy_1020] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1012 h))).fv) 1

theorem nb078_distinct_255 (h : Var) : (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1020 h) := by
  simpa only [nb078_alpha_dummy_1019, nb078_alpha_dummy_1020] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1012 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_256 : (nb078_alpha_dummy_1023) ∉ (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1023] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_257 : (nb078_alpha_dummy_1024) ∉ (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1024] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_258 : (nb078_alpha_dummy_1025) ∉ (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1025] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_259 : (nb078_alpha_dummy_1023) ≠ (nb078_alpha_dummy_1024) := by
  simpa only [nb078_alpha_dummy_1023, nb078_alpha_dummy_1024] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_260 : (nb078_alpha_dummy_1023) ≠ (nb078_alpha_dummy_1025) := by
  simpa only [nb078_alpha_dummy_1023, nb078_alpha_dummy_1025] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_261 : (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1025) := by
  simpa only [nb078_alpha_dummy_1024, nb078_alpha_dummy_1025] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_262 (h : Var) : (nb078_alpha_dummy_1026 h) ∉ (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1026] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_263 (h : Var) : (nb078_alpha_dummy_1027 h) ∉ (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1027] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_264 (h : Var) : (nb078_alpha_dummy_1028 h) ∉ (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1028] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_265 (h : Var) : (nb078_alpha_dummy_1026 h) ≠ (nb078_alpha_dummy_1027 h) := by
  simpa only [nb078_alpha_dummy_1026, nb078_alpha_dummy_1027] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_266 (h : Var) : (nb078_alpha_dummy_1026 h) ≠ (nb078_alpha_dummy_1028 h) := by
  simpa only [nb078_alpha_dummy_1026, nb078_alpha_dummy_1028] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_267 (h : Var) : (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1028 h) := by
  simpa only [nb078_alpha_dummy_1027, nb078_alpha_dummy_1028] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_268 : (nb078_alpha_dummy_1035) ∉ (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1024))).fv) := by
  simpa only [nb078_alpha_dummy_1035] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1024))).fv) 0

theorem nb078_fresh_269 : (nb078_alpha_dummy_1031) ∉ (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) := by
  simpa only [nb078_alpha_dummy_1031] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) 0

theorem nb078_fresh_270 : (nb078_alpha_dummy_1037) ∉ (((Class.cv (nb078_alpha_dummy_1025))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) := by
  simpa only [nb078_alpha_dummy_1037] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1025))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) 0

theorem nb078_fresh_271 (h : Var) : (nb078_alpha_dummy_1036 h) ∉ (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1027 h))).fv) := by
  simpa only [nb078_alpha_dummy_1036] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1027 h))).fv) 0

theorem nb078_fresh_272 (h : Var) : (nb078_alpha_dummy_1032 h) ∉ (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv) := by
  simpa only [nb078_alpha_dummy_1032] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv) 0

theorem nb078_fresh_273 (h : Var) : (nb078_alpha_dummy_1038 h) ∉ (((Class.cv (nb078_alpha_dummy_1028 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv) := by
  simpa only [nb078_alpha_dummy_1038] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1028 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv) 0

theorem nb078_fresh_274 : (nb078_alpha_dummy_109) ∉ (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_109] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_275 : (nb078_alpha_dummy_110) ∉ (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_110] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_276 : (nb078_alpha_dummy_111) ∉ (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_111] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_277 : (nb078_alpha_dummy_109) ≠ (nb078_alpha_dummy_110) := by
  simpa only [nb078_alpha_dummy_109, nb078_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_278 : (nb078_alpha_dummy_109) ≠ (nb078_alpha_dummy_111) := by
  simpa only [nb078_alpha_dummy_109, nb078_alpha_dummy_111] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_279 : (nb078_alpha_dummy_110) ≠ (nb078_alpha_dummy_111) := by
  simpa only [nb078_alpha_dummy_110, nb078_alpha_dummy_111] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_280 : (nb078_alpha_dummy_1057) ∉ (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) := by
  simpa only [nb078_alpha_dummy_1057] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) 0

theorem nb078_fresh_281 : (nb078_alpha_dummy_1058) ∉ (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) := by
  simpa only [nb078_alpha_dummy_1058] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) 1

theorem nb078_distinct_282 : (nb078_alpha_dummy_1057) ≠ (nb078_alpha_dummy_1058) := by
  simpa only [nb078_alpha_dummy_1057, nb078_alpha_dummy_1058] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_283 : (nb078_alpha_dummy_1093) ∉ (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) := by
  simpa only [nb078_alpha_dummy_1093] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) 0

theorem nb078_fresh_284 : (nb078_alpha_dummy_1094) ∉ (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) := by
  simpa only [nb078_alpha_dummy_1094] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) 1

theorem nb078_distinct_285 : (nb078_alpha_dummy_1093) ≠ (nb078_alpha_dummy_1094) := by
  simpa only [nb078_alpha_dummy_1093, nb078_alpha_dummy_1094] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_286 (f : Var) : (nb078_alpha_dummy_112 f) ∉ (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_112] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_287 (f : Var) : (nb078_alpha_dummy_113 f) ∉ (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_113] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_288 (f : Var) : (nb078_alpha_dummy_114 f) ∉ (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_114] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_289 (f : Var) : (nb078_alpha_dummy_112 f) ≠ (nb078_alpha_dummy_113 f) := by
  simpa only [nb078_alpha_dummy_112, nb078_alpha_dummy_113] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_290 (f : Var) : (nb078_alpha_dummy_112 f) ≠ (nb078_alpha_dummy_114 f) := by
  simpa only [nb078_alpha_dummy_112, nb078_alpha_dummy_114] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_291 (f : Var) : (nb078_alpha_dummy_113 f) ≠ (nb078_alpha_dummy_114 f) := by
  simpa only [nb078_alpha_dummy_113, nb078_alpha_dummy_114] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_292 : (nb078_alpha_dummy_1207) ∉ (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) := by
  simpa only [nb078_alpha_dummy_1207] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) 0

theorem nb078_fresh_293 : (nb078_alpha_dummy_1208) ∉ (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) := by
  simpa only [nb078_alpha_dummy_1208] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) 1

theorem nb078_distinct_294 : (nb078_alpha_dummy_1207) ≠ (nb078_alpha_dummy_1208) := by
  simpa only [nb078_alpha_dummy_1207, nb078_alpha_dummy_1208] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_295 (h : Var) : (nb078_alpha_dummy_1059 h) ∉ (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) := by
  simpa only [nb078_alpha_dummy_1059] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) 0

theorem nb078_fresh_296 (h : Var) : (nb078_alpha_dummy_1060 h) ∉ (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) := by
  simpa only [nb078_alpha_dummy_1060] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) 1

theorem nb078_distinct_297 (h : Var) : (nb078_alpha_dummy_1059 h) ≠ (nb078_alpha_dummy_1060 h) := by
  simpa only [nb078_alpha_dummy_1059, nb078_alpha_dummy_1060] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_298 (h : Var) : (nb078_alpha_dummy_1095 h) ∉ (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1054 h))).fv) := by
  simpa only [nb078_alpha_dummy_1095] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1054 h))).fv) 0

theorem nb078_fresh_299 (h : Var) : (nb078_alpha_dummy_1096 h) ∉ (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1054 h))).fv) := by
  simpa only [nb078_alpha_dummy_1096] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1054 h))).fv) 1

theorem nb078_distinct_300 (h : Var) : (nb078_alpha_dummy_1095 h) ≠ (nb078_alpha_dummy_1096 h) := by
  simpa only [nb078_alpha_dummy_1095, nb078_alpha_dummy_1096] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1054 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_301 (h : Var) : (nb078_alpha_dummy_1209 h) ∉ (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) := by
  simpa only [nb078_alpha_dummy_1209] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) 0

theorem nb078_fresh_302 (h : Var) : (nb078_alpha_dummy_1210 h) ∉ (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) := by
  simpa only [nb078_alpha_dummy_1210] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) 1

theorem nb078_distinct_303 (h : Var) : (nb078_alpha_dummy_1209 h) ≠ (nb078_alpha_dummy_1210 h) := by
  simpa only [nb078_alpha_dummy_1209, nb078_alpha_dummy_1210] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_304 : (nb078_alpha_dummy_1065) ∉ (((Class.cv (nb078_alpha_dummy_1058))).fv) := by
  simpa only [nb078_alpha_dummy_1065] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1058))).fv) 0

theorem nb078_fresh_305 : (nb078_alpha_dummy_1066) ∉ (((Class.cv (nb078_alpha_dummy_1058))).fv) := by
  simpa only [nb078_alpha_dummy_1066] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1058))).fv) 1

theorem nb078_distinct_306 : (nb078_alpha_dummy_1065) ≠ (nb078_alpha_dummy_1066) := by
  simpa only [nb078_alpha_dummy_1065, nb078_alpha_dummy_1066] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1058))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_307 (h : Var) : (nb078_alpha_dummy_1067 h) ∉ (((Class.cv (nb078_alpha_dummy_1060 h))).fv) := by
  simpa only [nb078_alpha_dummy_1067] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1060 h))).fv) 0

theorem nb078_fresh_308 (h : Var) : (nb078_alpha_dummy_1068 h) ∉ (((Class.cv (nb078_alpha_dummy_1060 h))).fv) := by
  simpa only [nb078_alpha_dummy_1068] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1060 h))).fv) 1

theorem nb078_distinct_309 (h : Var) : (nb078_alpha_dummy_1067 h) ≠ (nb078_alpha_dummy_1068 h) := by
  simpa only [nb078_alpha_dummy_1067, nb078_alpha_dummy_1068] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1060 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_310 : (nb078_alpha_dummy_1071) ∉ (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1071] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_311 : (nb078_alpha_dummy_1072) ∉ (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1072] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_312 : (nb078_alpha_dummy_1073) ∉ (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1073] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_313 : (nb078_alpha_dummy_1071) ≠ (nb078_alpha_dummy_1072) := by
  simpa only [nb078_alpha_dummy_1071, nb078_alpha_dummy_1072] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_314 : (nb078_alpha_dummy_1071) ≠ (nb078_alpha_dummy_1073) := by
  simpa only [nb078_alpha_dummy_1071, nb078_alpha_dummy_1073] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_315 : (nb078_alpha_dummy_1072) ≠ (nb078_alpha_dummy_1073) := by
  simpa only [nb078_alpha_dummy_1072, nb078_alpha_dummy_1073] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_316 (h : Var) : (nb078_alpha_dummy_1074 h) ∉ (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1074] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_317 (h : Var) : (nb078_alpha_dummy_1075 h) ∉ (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1075] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_318 (h : Var) : (nb078_alpha_dummy_1076 h) ∉ (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1076] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_319 (h : Var) : (nb078_alpha_dummy_1074 h) ≠ (nb078_alpha_dummy_1075 h) := by
  simpa only [nb078_alpha_dummy_1074, nb078_alpha_dummy_1075] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_320 (h : Var) : (nb078_alpha_dummy_1074 h) ≠ (nb078_alpha_dummy_1076 h) := by
  simpa only [nb078_alpha_dummy_1074, nb078_alpha_dummy_1076] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_321 (h : Var) : (nb078_alpha_dummy_1075 h) ≠ (nb078_alpha_dummy_1076 h) := by
  simpa only [nb078_alpha_dummy_1075, nb078_alpha_dummy_1076] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_322 : (nb078_alpha_dummy_1083) ∉ (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1072))).fv) := by
  simpa only [nb078_alpha_dummy_1083] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1072))).fv) 0

theorem nb078_fresh_323 : (nb078_alpha_dummy_1079) ∉ (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) := by
  simpa only [nb078_alpha_dummy_1079] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) 0

theorem nb078_fresh_324 : (nb078_alpha_dummy_1085) ∉ (((Class.cv (nb078_alpha_dummy_1073))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) := by
  simpa only [nb078_alpha_dummy_1085] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1073))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) 0

theorem nb078_fresh_325 (h : Var) : (nb078_alpha_dummy_1084 h) ∉ (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1075 h))).fv) := by
  simpa only [nb078_alpha_dummy_1084] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1075 h))).fv) 0

theorem nb078_fresh_326 (h : Var) : (nb078_alpha_dummy_1080 h) ∉ (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv) := by
  simpa only [nb078_alpha_dummy_1080] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv) 0

theorem nb078_fresh_327 (h : Var) : (nb078_alpha_dummy_1086 h) ∉ (((Class.cv (nb078_alpha_dummy_1076 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv) := by
  simpa only [nb078_alpha_dummy_1086] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1076 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1076 h))).fv) 0

theorem nb078_fresh_328 : (nb078_alpha_dummy_1101) ∉ (((Class.cv (nb078_alpha_dummy_1094))).fv) := by
  simpa only [nb078_alpha_dummy_1101] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1094))).fv) 0

theorem nb078_fresh_329 : (nb078_alpha_dummy_1102) ∉ (((Class.cv (nb078_alpha_dummy_1094))).fv) := by
  simpa only [nb078_alpha_dummy_1102] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1094))).fv) 1

theorem nb078_distinct_330 : (nb078_alpha_dummy_1101) ≠ (nb078_alpha_dummy_1102) := by
  simpa only [nb078_alpha_dummy_1101, nb078_alpha_dummy_1102] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1094))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_331 (h : Var) : (nb078_alpha_dummy_1103 h) ∉ (((Class.cv (nb078_alpha_dummy_1096 h))).fv) := by
  simpa only [nb078_alpha_dummy_1103] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1096 h))).fv) 0

theorem nb078_fresh_332 (h : Var) : (nb078_alpha_dummy_1104 h) ∉ (((Class.cv (nb078_alpha_dummy_1096 h))).fv) := by
  simpa only [nb078_alpha_dummy_1104] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1096 h))).fv) 1

theorem nb078_distinct_333 (h : Var) : (nb078_alpha_dummy_1103 h) ≠ (nb078_alpha_dummy_1104 h) := by
  simpa only [nb078_alpha_dummy_1103, nb078_alpha_dummy_1104] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1096 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_334 : (nb078_alpha_dummy_121) ∉ (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_110))).fv) := by
  simpa only [nb078_alpha_dummy_121] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_110))).fv) 0

theorem nb078_fresh_335 : (nb078_alpha_dummy_117) ∉ (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) := by
  simpa only [nb078_alpha_dummy_117] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) 0

theorem nb078_fresh_336 : (nb078_alpha_dummy_1107) ∉ (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1107] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_337 : (nb078_alpha_dummy_1108) ∉ (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1108] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_338 : (nb078_alpha_dummy_1109) ∉ (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1109] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_339 : (nb078_alpha_dummy_1107) ≠ (nb078_alpha_dummy_1108) := by
  simpa only [nb078_alpha_dummy_1107, nb078_alpha_dummy_1108] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_340 : (nb078_alpha_dummy_1107) ≠ (nb078_alpha_dummy_1109) := by
  simpa only [nb078_alpha_dummy_1107, nb078_alpha_dummy_1109] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_341 : (nb078_alpha_dummy_1108) ≠ (nb078_alpha_dummy_1109) := by
  simpa only [nb078_alpha_dummy_1108, nb078_alpha_dummy_1109] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_342 (h : Var) : (nb078_alpha_dummy_1110 h) ∉ (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1110] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_343 (h : Var) : (nb078_alpha_dummy_1111 h) ∉ (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1111] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_344 (h : Var) : (nb078_alpha_dummy_1112 h) ∉ (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1112] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_345 (h : Var) : (nb078_alpha_dummy_1110 h) ≠ (nb078_alpha_dummy_1111 h) := by
  simpa only [nb078_alpha_dummy_1110, nb078_alpha_dummy_1111] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_346 (h : Var) : (nb078_alpha_dummy_1110 h) ≠ (nb078_alpha_dummy_1112 h) := by
  simpa only [nb078_alpha_dummy_1110, nb078_alpha_dummy_1112] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_347 (h : Var) : (nb078_alpha_dummy_1111 h) ≠ (nb078_alpha_dummy_1112 h) := by
  simpa only [nb078_alpha_dummy_1111, nb078_alpha_dummy_1112] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_348 : (nb078_alpha_dummy_1119) ∉ (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1108))).fv) := by
  simpa only [nb078_alpha_dummy_1119] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1108))).fv) 0

theorem nb078_fresh_349 : (nb078_alpha_dummy_1115) ∉ (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) := by
  simpa only [nb078_alpha_dummy_1115] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) 0

theorem nb078_fresh_350 : (nb078_alpha_dummy_1121) ∉ (((Class.cv (nb078_alpha_dummy_1109))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) := by
  simpa only [nb078_alpha_dummy_1121] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1109))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) 0

theorem nb078_fresh_351 : (nb078_alpha_dummy_123) ∉ (((Class.cv (nb078_alpha_dummy_111))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) := by
  simpa only [nb078_alpha_dummy_123] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_111))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) 0

theorem nb078_fresh_352 (h : Var) : (nb078_alpha_dummy_1120 h) ∉ (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1111 h))).fv) := by
  simpa only [nb078_alpha_dummy_1120] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1111 h))).fv) 0

theorem nb078_fresh_353 (h : Var) : (nb078_alpha_dummy_1116 h) ∉ (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1112 h))).fv) := by
  simpa only [nb078_alpha_dummy_1116] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1112 h))).fv) 0

theorem nb078_fresh_354 (h : Var) : (nb078_alpha_dummy_1122 h) ∉ (((Class.cv (nb078_alpha_dummy_1112 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1112 h))).fv) := by
  simpa only [nb078_alpha_dummy_1122] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1112 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1112 h))).fv) 0

theorem nb078_fresh_355 : (nb078_alpha_dummy_1135) ∉ (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) := by
  simpa only [nb078_alpha_dummy_1135] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) 0

theorem nb078_fresh_356 : (nb078_alpha_dummy_1136) ∉ (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) := by
  simpa only [nb078_alpha_dummy_1136] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) 1

theorem nb078_distinct_357 : (nb078_alpha_dummy_1135) ≠ (nb078_alpha_dummy_1136) := by
  simpa only [nb078_alpha_dummy_1135, nb078_alpha_dummy_1136] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_358 (f : Var) : (nb078_alpha_dummy_122 f) ∉ (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_113 f))).fv) := by
  simpa only [nb078_alpha_dummy_122] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_113 f))).fv) 0

theorem nb078_fresh_359 (f : Var) : (nb078_alpha_dummy_118 f) ∉ (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) := by
  simpa only [nb078_alpha_dummy_118] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) 0

theorem nb078_fresh_360 : (nb078_alpha_dummy_1171) ∉ (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) := by
  simpa only [nb078_alpha_dummy_1171] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) 0

theorem nb078_fresh_361 : (nb078_alpha_dummy_1172) ∉ (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) := by
  simpa only [nb078_alpha_dummy_1172] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) 1

theorem nb078_distinct_362 : (nb078_alpha_dummy_1171) ≠ (nb078_alpha_dummy_1172) := by
  simpa only [nb078_alpha_dummy_1171, nb078_alpha_dummy_1172] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_363 (h : Var) : (nb078_alpha_dummy_1137 h) ∉ (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1132 h))).fv) := by
  simpa only [nb078_alpha_dummy_1137] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1132 h))).fv) 0

theorem nb078_fresh_364 (h : Var) : (nb078_alpha_dummy_1138 h) ∉ (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1132 h))).fv) := by
  simpa only [nb078_alpha_dummy_1138] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1132 h))).fv) 1

theorem nb078_distinct_365 (h : Var) : (nb078_alpha_dummy_1137 h) ≠ (nb078_alpha_dummy_1138 h) := by
  simpa only [nb078_alpha_dummy_1137, nb078_alpha_dummy_1138] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1132 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_366 (h : Var) : (nb078_alpha_dummy_1173 h) ∉ (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1131 h))).fv) := by
  simpa only [nb078_alpha_dummy_1173] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1131 h))).fv) 0

theorem nb078_fresh_367 (h : Var) : (nb078_alpha_dummy_1174 h) ∉ (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1131 h))).fv) := by
  simpa only [nb078_alpha_dummy_1174] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1131 h))).fv) 1

theorem nb078_distinct_368 (h : Var) : (nb078_alpha_dummy_1173 h) ≠ (nb078_alpha_dummy_1174 h) := by
  simpa only [nb078_alpha_dummy_1173, nb078_alpha_dummy_1174] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1131 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_369 : (nb078_alpha_dummy_1143) ∉ (((Class.cv (nb078_alpha_dummy_1136))).fv) := by
  simpa only [nb078_alpha_dummy_1143] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1136))).fv) 0

theorem nb078_fresh_370 : (nb078_alpha_dummy_1144) ∉ (((Class.cv (nb078_alpha_dummy_1136))).fv) := by
  simpa only [nb078_alpha_dummy_1144] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1136))).fv) 1

theorem nb078_distinct_371 : (nb078_alpha_dummy_1143) ≠ (nb078_alpha_dummy_1144) := by
  simpa only [nb078_alpha_dummy_1143, nb078_alpha_dummy_1144] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1136))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_372 (h : Var) : (nb078_alpha_dummy_1145 h) ∉ (((Class.cv (nb078_alpha_dummy_1138 h))).fv) := by
  simpa only [nb078_alpha_dummy_1145] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1138 h))).fv) 0

theorem nb078_fresh_373 (h : Var) : (nb078_alpha_dummy_1146 h) ∉ (((Class.cv (nb078_alpha_dummy_1138 h))).fv) := by
  simpa only [nb078_alpha_dummy_1146] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1138 h))).fv) 1

theorem nb078_distinct_374 (h : Var) : (nb078_alpha_dummy_1145 h) ≠ (nb078_alpha_dummy_1146 h) := by
  simpa only [nb078_alpha_dummy_1145, nb078_alpha_dummy_1146] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1138 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_375 (f : Var) : (nb078_alpha_dummy_124 f) ∉ (((Class.cv (nb078_alpha_dummy_114 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) := by
  simpa only [nb078_alpha_dummy_124] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_114 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) 0

theorem nb078_fresh_376 : (nb078_alpha_dummy_1149) ∉ (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1149] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_377 : (nb078_alpha_dummy_1150) ∉ (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1150] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_378 : (nb078_alpha_dummy_1151) ∉ (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1151] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_379 : (nb078_alpha_dummy_1149) ≠ (nb078_alpha_dummy_1150) := by
  simpa only [nb078_alpha_dummy_1149, nb078_alpha_dummy_1150] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_380 : (nb078_alpha_dummy_1149) ≠ (nb078_alpha_dummy_1151) := by
  simpa only [nb078_alpha_dummy_1149, nb078_alpha_dummy_1151] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_381 : (nb078_alpha_dummy_1150) ≠ (nb078_alpha_dummy_1151) := by
  simpa only [nb078_alpha_dummy_1150, nb078_alpha_dummy_1151] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_382 (h : Var) : (nb078_alpha_dummy_1152 h) ∉ (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1152] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_383 (h : Var) : (nb078_alpha_dummy_1153 h) ∉ (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1153] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_384 (h : Var) : (nb078_alpha_dummy_1154 h) ∉ (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1154] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_385 (h : Var) : (nb078_alpha_dummy_1152 h) ≠ (nb078_alpha_dummy_1153 h) := by
  simpa only [nb078_alpha_dummy_1152, nb078_alpha_dummy_1153] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_386 (h : Var) : (nb078_alpha_dummy_1152 h) ≠ (nb078_alpha_dummy_1154 h) := by
  simpa only [nb078_alpha_dummy_1152, nb078_alpha_dummy_1154] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_387 (h : Var) : (nb078_alpha_dummy_1153 h) ≠ (nb078_alpha_dummy_1154 h) := by
  simpa only [nb078_alpha_dummy_1153, nb078_alpha_dummy_1154] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_388 : (nb078_alpha_dummy_1161) ∉ (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1150))).fv) := by
  simpa only [nb078_alpha_dummy_1161] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1150))).fv) 0

theorem nb078_fresh_389 : (nb078_alpha_dummy_1157) ∉ (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) := by
  simpa only [nb078_alpha_dummy_1157] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) 0

theorem nb078_fresh_390 : (nb078_alpha_dummy_1163) ∉ (((Class.cv (nb078_alpha_dummy_1151))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) := by
  simpa only [nb078_alpha_dummy_1163] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1151))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) 0

theorem nb078_fresh_391 (h : Var) : (nb078_alpha_dummy_1162 h) ∉ (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1153 h))).fv) := by
  simpa only [nb078_alpha_dummy_1162] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1153 h))).fv) 0

theorem nb078_fresh_392 (h : Var) : (nb078_alpha_dummy_1158 h) ∉ (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1154 h))).fv) := by
  simpa only [nb078_alpha_dummy_1158] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1154 h))).fv) 0

theorem nb078_fresh_393 (h : Var) : (nb078_alpha_dummy_1164 h) ∉ (((Class.cv (nb078_alpha_dummy_1154 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1154 h))).fv) := by
  simpa only [nb078_alpha_dummy_1164] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1154 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1154 h))).fv) 0

theorem nb078_fresh_394 : (nb078_alpha_dummy_1179) ∉ (((Class.cv (nb078_alpha_dummy_1172))).fv) := by
  simpa only [nb078_alpha_dummy_1179] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1172))).fv) 0

theorem nb078_fresh_395 : (nb078_alpha_dummy_1180) ∉ (((Class.cv (nb078_alpha_dummy_1172))).fv) := by
  simpa only [nb078_alpha_dummy_1180] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1172))).fv) 1

theorem nb078_distinct_396 : (nb078_alpha_dummy_1179) ≠ (nb078_alpha_dummy_1180) := by
  simpa only [nb078_alpha_dummy_1179, nb078_alpha_dummy_1180] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1172))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_397 (h : Var) : (nb078_alpha_dummy_1181 h) ∉ (((Class.cv (nb078_alpha_dummy_1174 h))).fv) := by
  simpa only [nb078_alpha_dummy_1181] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1174 h))).fv) 0

theorem nb078_fresh_398 (h : Var) : (nb078_alpha_dummy_1182 h) ∉ (((Class.cv (nb078_alpha_dummy_1174 h))).fv) := by
  simpa only [nb078_alpha_dummy_1182] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1174 h))).fv) 1

theorem nb078_distinct_399 (h : Var) : (nb078_alpha_dummy_1181 h) ≠ (nb078_alpha_dummy_1182 h) := by
  simpa only [nb078_alpha_dummy_1181, nb078_alpha_dummy_1182] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1174 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_400 : (nb078_alpha_dummy_1185) ∉ (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1185] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_401 : (nb078_alpha_dummy_1186) ∉ (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1186] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_402 : (nb078_alpha_dummy_1187) ∉ (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_1187] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_403 : (nb078_alpha_dummy_1185) ≠ (nb078_alpha_dummy_1186) := by
  simpa only [nb078_alpha_dummy_1185, nb078_alpha_dummy_1186] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
