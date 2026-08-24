import NAR4C057C001Part004

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

theorem nb057_fresh_322 : (nb057_alpha_dummy_072) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv) := by
  simpa only [nb057_alpha_dummy_072] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv) 0

theorem nb057_fresh_323 (f : Var) : (nb057_alpha_dummy_073 f) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv) := by
  simpa only [nb057_alpha_dummy_073] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv) 0

theorem nb057_fresh_324 : (nb057_alpha_dummy_108) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv) := by
  simpa only [nb057_alpha_dummy_108] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv) 0

theorem nb057_fresh_325 (f : Var) : (nb057_alpha_dummy_109 f) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv) := by
  simpa only [nb057_alpha_dummy_109] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv) 0

theorem nb057_fresh_326 : (nb057_alpha_dummy_150) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv) := by
  simpa only [nb057_alpha_dummy_150] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv) 0

theorem nb057_fresh_327 (f : Var) : (nb057_alpha_dummy_151 f) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv) := by
  simpa only [nb057_alpha_dummy_151] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv) 0

theorem nb057_fresh_328 : (nb057_alpha_dummy_186) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv) := by
  simpa only [nb057_alpha_dummy_186] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv) 0

theorem nb057_fresh_329 (f : Var) : (nb057_alpha_dummy_187 f) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv) := by
  simpa only [nb057_alpha_dummy_187] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv) 0

theorem nb057_fresh_330 : (nb057_alpha_dummy_222) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv) := by
  simpa only [nb057_alpha_dummy_222] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv) 0

theorem nb057_fresh_331 (f : Var) : (nb057_alpha_dummy_223 f) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv) := by
  simpa only [nb057_alpha_dummy_223] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv) 0

theorem nb057_fresh_332 : (nb057_alpha_dummy_262) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv) := by
  simpa only [nb057_alpha_dummy_262] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv) 0

theorem nb057_fresh_333 (f : Var) : (nb057_alpha_dummy_263 f) ∉ (((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv) := by
  simpa only [nb057_alpha_dummy_263] using freshVar_not_mem (((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv) 0

theorem nb057_fresh_334 : (nb057_alpha_dummy_040) ∉ (((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv) := by
  simpa only [nb057_alpha_dummy_040] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv) 0

theorem nb057_fresh_335 (f : Var) : (nb057_alpha_dummy_041 f) ∉ (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) := by
  simpa only [nb057_alpha_dummy_041] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0

theorem nb057_fresh_336 : (nb057_alpha_dummy_038) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv) := by
  simpa only [nb057_alpha_dummy_038] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv) 0

theorem nb057_fresh_337 (f : Var) (a : Var) : (nb057_alpha_dummy_039 f a) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv) := by
  simpa only [nb057_alpha_dummy_039] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv) 0

theorem nb057_fresh_338 : (nb057_alpha_dummy_086) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv) := by
  simpa only [nb057_alpha_dummy_086] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv) 0

theorem nb057_fresh_339 (f : Var) : (nb057_alpha_dummy_087 f) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv) := by
  simpa only [nb057_alpha_dummy_087] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv) 0

theorem nb057_fresh_340 : (nb057_alpha_dummy_122) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv) := by
  simpa only [nb057_alpha_dummy_122] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv) 0

theorem nb057_fresh_341 (f : Var) : (nb057_alpha_dummy_123 f) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv) := by
  simpa only [nb057_alpha_dummy_123] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv) 0

theorem nb057_fresh_342 : (nb057_alpha_dummy_164) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv) := by
  simpa only [nb057_alpha_dummy_164] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv) 0

theorem nb057_fresh_343 (f : Var) : (nb057_alpha_dummy_165 f) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv) := by
  simpa only [nb057_alpha_dummy_165] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv) 0

theorem nb057_fresh_344 : (nb057_alpha_dummy_200) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv) := by
  simpa only [nb057_alpha_dummy_200] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv) 0

theorem nb057_fresh_345 (f : Var) : (nb057_alpha_dummy_201 f) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv) := by
  simpa only [nb057_alpha_dummy_201] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv) 0

theorem nb057_fresh_346 : (nb057_alpha_dummy_236) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv) := by
  simpa only [nb057_alpha_dummy_236] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv) 0

theorem nb057_fresh_347 (f : Var) : (nb057_alpha_dummy_237 f) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv) := by
  simpa only [nb057_alpha_dummy_237] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv) 0

theorem nb057_fresh_348 : (nb057_alpha_dummy_276) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv) := by
  simpa only [nb057_alpha_dummy_276] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv) 0

theorem nb057_fresh_349 (f : Var) : (nb057_alpha_dummy_277 f) ∉ (((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv) := by
  simpa only [nb057_alpha_dummy_277] using freshVar_not_mem (((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv) 0

theorem nb057_fresh_350 : (nb057_alpha_dummy_002) ∉ (({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var) ∪ ((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv) := by
  simpa only [nb057_alpha_dummy_002] using freshVar_not_mem (({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var) ∪ ((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv) 0

theorem nb057_fresh_351 : (nb057_alpha_dummy_050) ∉ (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))) (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv) := by
  simpa only [nb057_alpha_dummy_050] using freshVar_not_mem (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))) (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv) 0

theorem nb057_fresh_352 (f : Var) : (nb057_alpha_dummy_051 f) ∉ (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb057_alpha_dummy_049 f))) (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_048 f)))))).fv) := by
  simpa only [nb057_alpha_dummy_051] using freshVar_not_mem (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb057_alpha_dummy_049 f))) (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_048 f)))))).fv) 0

theorem nb057_fresh_353 : (nb057_alpha_dummy_128) ∉ (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_124)))).fv) := by
  simpa only [nb057_alpha_dummy_128] using freshVar_not_mem (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_124)))).fv) 0

theorem nb057_fresh_354 (f : Var) : (nb057_alpha_dummy_129 f) ∉ (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_126 f)))).fv) := by
  simpa only [nb057_alpha_dummy_129] using freshVar_not_mem (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_126 f)))).fv) 0

theorem nb057_fresh_355 (f : Var) (a : Var) : (nb057_alpha_dummy_003 f a) ∉ (({f} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wfn (Class.cv f) (Class.cv a))).fv) := by
  simpa only [nb057_alpha_dummy_003] using freshVar_not_mem (({f} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wfn (Class.cv f) (Class.cv a))).fv) 0

theorem nb057_fresh_356 : (nb057_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb057_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb057_fresh_357 : (nb057_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb057_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb057_distinct_358 : (nb057_alpha_dummy_000) ≠ (nb057_alpha_dummy_001) := by
  simpa only [nb057_alpha_dummy_000, nb057_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb057_support_mem_0000 : (nb057_alpha_dummy_001) ∈ (({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var) ∪ ((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0001 (f : Var) (a : Var) : f ∈ (({f} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wfn (Class.cv f) (Class.cv a))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0002 : (nb057_alpha_dummy_000) ∈ (({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var) ∪ ((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0003 (f : Var) (a : Var) : a ∈ (({f} : Finset Var) ∪ ({a} : Finset Var) ∪ ((syn_wfn (Class.cv f) (Class.cv a))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0004 : (nb057_alpha_dummy_001) ∈ (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0005 : (nb057_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0006 (f : Var) (a : Var) : f ∈ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0007 (f : Var) (a : Var) : f ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0008 : (nb057_alpha_dummy_001) ∈ (((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0009 (f : Var) (a : Var) : f ∈ (((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0010 : (nb057_alpha_dummy_005) ∈ (((Class.cv (nb057_alpha_dummy_005))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0011 (f : Var) (a : Var) : (nb057_alpha_dummy_007 f a) ∈ (((Class.cv (nb057_alpha_dummy_007 f a))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0012 : (nb057_alpha_dummy_012) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_012)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_012)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_012))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0013 (f : Var) (a : Var) : (nb057_alpha_dummy_014 f a) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_014 f a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_014 f a)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_014 f a))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0014 : (nb057_alpha_dummy_012) ∈ (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0015 (f : Var) (a : Var) : (nb057_alpha_dummy_014 f a) ∈ (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0016 : (nb057_alpha_dummy_019) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0017 (f : Var) (a : Var) : (nb057_alpha_dummy_022 f a) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0018 : (nb057_alpha_dummy_019) ∈ (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0019 (f : Var) (a : Var) : (nb057_alpha_dummy_022 f a) ∈ (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_023 f a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0020 : (nb057_alpha_dummy_020) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0021 (f : Var) (a : Var) : (nb057_alpha_dummy_023 f a) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a)) (Class.cv (nb057_alpha_dummy_023 f a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0022 : (nb057_alpha_dummy_020) ∈ (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0023 (f : Var) (a : Var) : (nb057_alpha_dummy_023 f a) ∈ (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_023 f a))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0024 : (nb057_alpha_dummy_019) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_019)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_020)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0025 (f : Var) (a : Var) : (nb057_alpha_dummy_022 f a) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_022 f a)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_023 f a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0026 : (nb057_alpha_dummy_019) ∈ (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_019))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0027 (f : Var) (a : Var) : (nb057_alpha_dummy_022 f a) ∈ (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_022 f a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0028 : (nb057_alpha_dummy_020) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_019)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_020)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0029 (f : Var) (a : Var) : (nb057_alpha_dummy_023 f a) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_022 f a)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_023 f a)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0030 : (nb057_alpha_dummy_020) ∈ (((Class.cv (nb057_alpha_dummy_020))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0031 (f : Var) (a : Var) : (nb057_alpha_dummy_023 f a) ∈ (((Class.cv (nb057_alpha_dummy_023 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_023 f a))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0032 : (nb057_alpha_dummy_000) ∈ (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0033 : (nb057_alpha_dummy_000) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0034 (f : Var) (a : Var) : a ∈ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0035 (f : Var) (a : Var) : a ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0036 : (nb057_alpha_dummy_000) ∈ (((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004) (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000)) (Wff.classEq (Class.cv (nb057_alpha_dummy_004)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0037 (f : Var) (a : Var) : a ∈ (((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a) (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0038 : (nb057_alpha_dummy_005) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_005))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0039 (f : Var) (a : Var) : (nb057_alpha_dummy_007 f a) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0040 : (nb057_alpha_dummy_005) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0041 (f : Var) (a : Var) : (nb057_alpha_dummy_007 f a) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0042 : (nb057_alpha_dummy_044) ∈ (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))) (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0043 (f : Var) : (nb057_alpha_dummy_047 f) ∈ (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb057_alpha_dummy_049 f))) (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_048 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0044 : (nb057_alpha_dummy_045) ∈ (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))) (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0045 (f : Var) : (nb057_alpha_dummy_048 f) ∈ (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb057_alpha_dummy_049 f))) (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_048 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0046 : (nb057_alpha_dummy_044) ∈ (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0047 : (nb057_alpha_dummy_044) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0048 (f : Var) : (nb057_alpha_dummy_047 f) ∈ (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0049 (f : Var) : (nb057_alpha_dummy_047 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0050 : (nb057_alpha_dummy_044) ∈ (((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0051 (f : Var) : (nb057_alpha_dummy_047 f) ∈ (((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0052 : (nb057_alpha_dummy_053) ∈ (((Class.cv (nb057_alpha_dummy_053))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0053 (f : Var) : (nb057_alpha_dummy_055 f) ∈ (((Class.cv (nb057_alpha_dummy_055 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0054 : (nb057_alpha_dummy_060) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_060)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_060))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0055 (f : Var) : (nb057_alpha_dummy_062 f) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_062 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_062 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0056 : (nb057_alpha_dummy_060) ∈ (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0057 (f : Var) : (nb057_alpha_dummy_062 f) ∈ (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0058 : (nb057_alpha_dummy_067) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0059 (f : Var) : (nb057_alpha_dummy_070 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0060 : (nb057_alpha_dummy_067) ∈ (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0061 (f : Var) : (nb057_alpha_dummy_070 f) ∈ (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0062 : (nb057_alpha_dummy_068) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0063 (f : Var) : (nb057_alpha_dummy_071 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0064 : (nb057_alpha_dummy_068) ∈ (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0065 (f : Var) : (nb057_alpha_dummy_071 f) ∈ (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0066 : (nb057_alpha_dummy_067) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_067)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_068)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0067 (f : Var) : (nb057_alpha_dummy_070 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_070 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_071 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0068 : (nb057_alpha_dummy_067) ∈ (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_067))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0069 (f : Var) : (nb057_alpha_dummy_070 f) ∈ (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_070 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0070 : (nb057_alpha_dummy_068) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_067)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_068)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0071 (f : Var) : (nb057_alpha_dummy_071 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_070 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_071 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0072 : (nb057_alpha_dummy_068) ∈ (((Class.cv (nb057_alpha_dummy_068))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0073 (f : Var) : (nb057_alpha_dummy_071 f) ∈ (((Class.cv (nb057_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0074 : (nb057_alpha_dummy_045) ∈ (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0075 : (nb057_alpha_dummy_045) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cphi (Class.cv (nb057_alpha_dummy_053)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0076 (f : Var) : (nb057_alpha_dummy_048 f) ∈ (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0077 (f : Var) : (nb057_alpha_dummy_048 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0078 : (nb057_alpha_dummy_045) ∈ (((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0079 (f : Var) : (nb057_alpha_dummy_048 f) ∈ (((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0080 : (nb057_alpha_dummy_053) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_053))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0081 (f : Var) : (nb057_alpha_dummy_055 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0082 : (nb057_alpha_dummy_053) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0083 (f : Var) : (nb057_alpha_dummy_055 f) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0084 : (nb057_alpha_dummy_044) ∈ (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0085 : (nb057_alpha_dummy_044) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0086 (f : Var) : (nb057_alpha_dummy_047 f) ∈ (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0087 (f : Var) : (nb057_alpha_dummy_047 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0088 : (nb057_alpha_dummy_044) ∈ (((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0089 (f : Var) : (nb057_alpha_dummy_047 f) ∈ (((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0090 : (nb057_alpha_dummy_089) ∈ (((Class.cv (nb057_alpha_dummy_089))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0091 (f : Var) : (nb057_alpha_dummy_091 f) ∈ (((Class.cv (nb057_alpha_dummy_091 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0092 : (nb057_alpha_dummy_096) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_096))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0093 (f : Var) : (nb057_alpha_dummy_098 f) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_098 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0094 : (nb057_alpha_dummy_096) ∈ (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0095 (f : Var) : (nb057_alpha_dummy_098 f) ∈ (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0096 : (nb057_alpha_dummy_103) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0097 (f : Var) : (nb057_alpha_dummy_106 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0098 : (nb057_alpha_dummy_103) ∈ (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0099 (f : Var) : (nb057_alpha_dummy_106 f) ∈ (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0100 : (nb057_alpha_dummy_104) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0101 (f : Var) : (nb057_alpha_dummy_107 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0102 : (nb057_alpha_dummy_104) ∈ (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
