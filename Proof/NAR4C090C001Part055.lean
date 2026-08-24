import NAR4C090C001Part054

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

noncomputable def nb090_split_alpha_0032 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_369 A)) (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_369 A)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_370 h)) (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_370 h)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0344 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0345 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0344 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0345 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0374 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0375 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0372 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0373 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_338 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_340 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0348 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0349 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0348 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0349 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0346 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0347 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A), (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)), ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0113 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0352 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0353 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0350 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0351 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0356 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0357 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0354 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0355 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0352 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0353 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0350 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0351 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0356 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0357 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0354 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0355 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A), (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)), ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0114 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0360 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0361 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0358 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0359 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0360 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0361 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0358 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0359 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0364 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0365 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0362 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0363 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0364 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0365 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0362 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0363 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0346 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0347 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0115 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0346 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0347 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0346 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0347 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0115 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0344 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0345 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0344 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0345 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0374 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0375 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0372 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0373 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_338 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_340 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0348 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0349 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0348 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0349 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0346 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0347 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A), (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)), ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0113 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0352 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0353 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0350 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0351 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0356 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0357 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0354 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0355 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0352 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0353 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0350 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0351 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0356 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0357 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0354 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0355 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A), (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)), ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0114 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0360 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0361 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0358 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0359 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0360 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0361 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0358 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0359 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0364 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0365 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0362 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0363 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0364 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0365 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0362 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0363 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0346 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0347 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0115 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0346 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0347 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0346 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0347 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_371 A), (nb090_alpha_dummy_372 h)), ((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0115 v u A h)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_369 A), (nb090_alpha_dummy_370 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_367 A), (nb090_alpha_dummy_368 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0116 v u A h)))))

theorem nb090_compact_fv_empty_0280 (A : Class) : (nb090_alpha_dummy_397 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0976 (A : Class) : (nb090_alpha_dummy_397 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_397, fv_syn_c1c] using (nb090_compact_fv_empty_0280 A)

theorem nb090_compact_fv_empty_0281 (v : Var) : (nb090_alpha_dummy_400 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0977 (v : Var) : (nb090_alpha_dummy_400 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_400, fv_syn_c1c] using (nb090_compact_fv_empty_0281 v)

theorem nb090_compact_fv_empty_0282 (A : Class) : (nb090_alpha_dummy_396 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0978 (A : Class) : (nb090_alpha_dummy_396 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_396, fv_syn_c1c] using (nb090_compact_fv_empty_0282 A)

theorem nb090_compact_fv_empty_0283 (v : Var) : (nb090_alpha_dummy_399 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0979 (v : Var) : (nb090_alpha_dummy_399 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_399, fv_syn_c1c] using (nb090_compact_fv_empty_0283 v)

theorem nb090_compact_fv_empty_0284 (A : Class) : (nb090_alpha_dummy_395 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0980 (A : Class) : (nb090_alpha_dummy_395 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_395, fv_syn_c1c] using (nb090_compact_fv_empty_0284 A)

theorem nb090_compact_fv_empty_0285 (v : Var) : (nb090_alpha_dummy_398 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0981 (v : Var) : (nb090_alpha_dummy_398 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_398, fv_syn_c1c] using (nb090_compact_fv_empty_0285 v)

theorem nb090_compact_fv_empty_0286 (A : Class) : (nb090_alpha_dummy_393 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0982 (A : Class) : (nb090_alpha_dummy_393 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_393, fv_syn_c1c] using (nb090_compact_fv_empty_0286 A)

theorem nb090_compact_fv_empty_0287 (v : Var) : (nb090_alpha_dummy_394 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0983 (v : Var) : (nb090_alpha_dummy_394 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_394, fv_syn_c1c] using (nb090_compact_fv_empty_0287 v)

theorem nb090_compact_fv_empty_0288 (A : Class) : (nb090_alpha_dummy_389 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0984 (A : Class) : (nb090_alpha_dummy_389 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_389, fv_syn_c1c] using (nb090_compact_fv_empty_0288 A)

theorem nb090_compact_fv_empty_0289 (v : Var) : (nb090_alpha_dummy_391 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0985 (v : Var) : (nb090_alpha_dummy_391 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_391, fv_syn_c1c] using (nb090_compact_fv_empty_0289 v)

theorem nb090_compact_fv_empty_0290 (A : Class) : (nb090_alpha_dummy_390 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0986 (A : Class) : (nb090_alpha_dummy_390 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_390, fv_syn_c1c] using (nb090_compact_fv_empty_0290 A)

theorem nb090_compact_fv_empty_0291 (v : Var) : (nb090_alpha_dummy_392 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0987 (v : Var) : (nb090_alpha_dummy_392 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_392, fv_syn_c1c] using (nb090_compact_fv_empty_0291 v)

theorem nb090_compact_fv_empty_0292 (A : Class) : (nb090_alpha_dummy_382 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0988 (A : Class) : (nb090_alpha_dummy_382 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_382, fv_syn_c1c] using (nb090_compact_fv_empty_0292 A)

theorem nb090_compact_fv_empty_0293 (v : Var) : (nb090_alpha_dummy_384 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0989 (v : Var) : (nb090_alpha_dummy_384 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_384, fv_syn_c1c] using (nb090_compact_fv_empty_0293 v)

theorem nb090_compact_fv_empty_0294 (A : Class) : (nb090_alpha_dummy_381 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0990 (A : Class) : (nb090_alpha_dummy_381 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_381, fv_syn_c1c] using (nb090_compact_fv_empty_0294 A)

theorem nb090_compact_fv_empty_0295 (v : Var) : (nb090_alpha_dummy_383 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0991 (v : Var) : (nb090_alpha_dummy_383 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_383, fv_syn_c1c] using (nb090_compact_fv_empty_0295 v)

theorem nb090_compact_fv_empty_0296 (A : Class) : (nb090_alpha_dummy_387 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0992 (A : Class) : (nb090_alpha_dummy_387 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_387, fv_syn_c1c] using (nb090_compact_fv_empty_0296 A)

theorem nb090_compact_fv_empty_0297 (v : Var) : (nb090_alpha_dummy_388 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0993 (v : Var) : (nb090_alpha_dummy_388 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_388, fv_syn_c1c] using (nb090_compact_fv_empty_0297 v)

theorem nb090_compact_fv_empty_0298 (A : Class) : (nb090_alpha_dummy_385 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0994 (A : Class) : (nb090_alpha_dummy_385 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_385, fv_syn_c1c] using (nb090_compact_fv_empty_0298 A)

theorem nb090_compact_fv_empty_0299 (v : Var) : (nb090_alpha_dummy_386 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0995 (v : Var) : (nb090_alpha_dummy_386 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_386, fv_syn_c1c] using (nb090_compact_fv_empty_0299 v)

theorem nb090_compact_fv_empty_0300 (A : Class) : (nb090_alpha_dummy_373 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0996 (A : Class) : (nb090_alpha_dummy_373 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_373, fv_syn_c1c] using (nb090_compact_fv_empty_0300 A)

theorem nb090_compact_fv_empty_0301 (v : Var) : (nb090_alpha_dummy_374 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0997 (v : Var) : (nb090_alpha_dummy_374 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_374, fv_syn_c1c] using (nb090_compact_fv_empty_0301 v)

theorem nb090_compact_fv_empty_0302 (A : Class) : (nb090_alpha_dummy_375 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0998 (A : Class) : (nb090_alpha_dummy_375 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_375, fv_syn_c1c] using (nb090_compact_fv_empty_0302 A)

theorem nb090_compact_fv_empty_0303 (v : Var) : (nb090_alpha_dummy_376 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0999 (v : Var) : (nb090_alpha_dummy_376 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_376, fv_syn_c1c] using (nb090_compact_fv_empty_0303 v)

theorem nb090_compact_fv_empty_0304 (A : Class) : (nb090_alpha_dummy_378 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1000 (A : Class) : (nb090_alpha_dummy_378 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_378, fv_syn_c1c] using (nb090_compact_fv_empty_0304 A)

theorem nb090_compact_fv_empty_0305 (v : Var) : (nb090_alpha_dummy_380 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1001 (v : Var) : (nb090_alpha_dummy_380 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_380, fv_syn_c1c] using (nb090_compact_fv_empty_0305 v)

theorem nb090_compact_fv_empty_0306 (A : Class) : (nb090_alpha_dummy_377 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1002 (A : Class) : (nb090_alpha_dummy_377 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_377, fv_syn_c1c] using (nb090_compact_fv_empty_0306 A)

theorem nb090_compact_fv_empty_0307 (v : Var) : (nb090_alpha_dummy_379 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1003 (v : Var) : (nb090_alpha_dummy_379 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_379, fv_syn_c1c] using (nb090_compact_fv_empty_0307 v)

theorem nb090_compact_envfresh_0117 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_397 A), (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A), (nb090_alpha_dummy_399 v)), ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)), ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)), ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)), ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_397 A) (nb090_alpha_dummy_400 v) (nb090_wpp_notmem_0976 A) (nb090_wpp_notmem_0977 v) (TEnvFresh.consFresh (nb090_alpha_dummy_396 A) (nb090_alpha_dummy_399 v) (nb090_wpp_notmem_0978 A) (nb090_wpp_notmem_0979 v) (TEnvFresh.consFresh (nb090_alpha_dummy_395 A) (nb090_alpha_dummy_398 v) (nb090_wpp_notmem_0980 A) (nb090_wpp_notmem_0981 v) (TEnvFresh.consFresh (nb090_alpha_dummy_393 A) (nb090_alpha_dummy_394 v) (nb090_wpp_notmem_0982 A) (nb090_wpp_notmem_0983 v) (TEnvFresh.consFresh (nb090_alpha_dummy_389 A) (nb090_alpha_dummy_391 v) (nb090_wpp_notmem_0984 A) (nb090_wpp_notmem_0985 v) (TEnvFresh.consFresh (nb090_alpha_dummy_390 A) (nb090_alpha_dummy_392 v) (nb090_wpp_notmem_0986 A) (nb090_wpp_notmem_0987 v) (TEnvFresh.consFresh (nb090_alpha_dummy_382 A) (nb090_alpha_dummy_384 v) (nb090_wpp_notmem_0988 A) (nb090_wpp_notmem_0989 v) (TEnvFresh.consFresh (nb090_alpha_dummy_381 A) (nb090_alpha_dummy_383 v) (nb090_wpp_notmem_0990 A) (nb090_wpp_notmem_0991 v) (TEnvFresh.consFresh (nb090_alpha_dummy_387 A) (nb090_alpha_dummy_388 v) (nb090_wpp_notmem_0992 A) (nb090_wpp_notmem_0993 v) (TEnvFresh.consFresh (nb090_alpha_dummy_385 A) (nb090_alpha_dummy_386 v) (nb090_wpp_notmem_0994 A) (nb090_wpp_notmem_0995 v) (TEnvFresh.consFresh (nb090_alpha_dummy_373 A) (nb090_alpha_dummy_374 v) (nb090_wpp_notmem_0996 A) (nb090_wpp_notmem_0997 v) (TEnvFresh.consFresh (nb090_alpha_dummy_375 A) (nb090_alpha_dummy_376 v) (nb090_wpp_notmem_0998 A) (nb090_wpp_notmem_0999 v) (TEnvFresh.consFresh (nb090_alpha_dummy_378 A) (nb090_alpha_dummy_380 v) (nb090_wpp_notmem_1000 A) (nb090_wpp_notmem_1001 v) (TEnvFresh.consFresh (nb090_alpha_dummy_377 A) (nb090_alpha_dummy_379 v) (nb090_wpp_notmem_1002 A) (nb090_wpp_notmem_1003 v) (TEnvFresh.consFresh (nb090_alpha_dummy_331 A) (nb090_alpha_dummy_332 v h) (nb090_wpp_notmem_0886 A) (nb090_wpp_notmem_0887 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_329 A) (nb090_alpha_dummy_330 v h) (nb090_wpp_notmem_0888 A) (nb090_wpp_notmem_0889 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb090_wpp_refl_0117 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_397 A), (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A), (nb090_alpha_dummy_399 v)), ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)), ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)), ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)), ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0117 v u A h)

theorem nb090_wpp_notmem_1004 (A : Class) : (nb090_alpha_dummy_397 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_397, fv_syn_c0] using (nb090_compact_fv_empty_0280 A)

theorem nb090_wpp_notmem_1005 (v : Var) : (nb090_alpha_dummy_400 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_400, fv_syn_c0] using (nb090_compact_fv_empty_0281 v)

theorem nb090_wpp_notmem_1006 (A : Class) : (nb090_alpha_dummy_396 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_396, fv_syn_c0] using (nb090_compact_fv_empty_0282 A)

theorem nb090_wpp_notmem_1007 (v : Var) : (nb090_alpha_dummy_399 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_399, fv_syn_c0] using (nb090_compact_fv_empty_0283 v)

theorem nb090_wpp_notmem_1008 (A : Class) : (nb090_alpha_dummy_395 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_395, fv_syn_c0] using (nb090_compact_fv_empty_0284 A)

theorem nb090_wpp_notmem_1009 (v : Var) : (nb090_alpha_dummy_398 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_398, fv_syn_c0] using (nb090_compact_fv_empty_0285 v)

theorem nb090_wpp_notmem_1010 (A : Class) : (nb090_alpha_dummy_393 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_393, fv_syn_c0] using (nb090_compact_fv_empty_0286 A)

theorem nb090_wpp_notmem_1011 (v : Var) : (nb090_alpha_dummy_394 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_394, fv_syn_c0] using (nb090_compact_fv_empty_0287 v)

theorem nb090_wpp_notmem_1012 (A : Class) : (nb090_alpha_dummy_389 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_389, fv_syn_c0] using (nb090_compact_fv_empty_0288 A)

theorem nb090_wpp_notmem_1013 (v : Var) : (nb090_alpha_dummy_391 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_391, fv_syn_c0] using (nb090_compact_fv_empty_0289 v)

theorem nb090_wpp_notmem_1014 (A : Class) : (nb090_alpha_dummy_390 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_390, fv_syn_c0] using (nb090_compact_fv_empty_0290 A)

theorem nb090_wpp_notmem_1015 (v : Var) : (nb090_alpha_dummy_392 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_392, fv_syn_c0] using (nb090_compact_fv_empty_0291 v)

theorem nb090_wpp_notmem_1016 (A : Class) : (nb090_alpha_dummy_382 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_382, fv_syn_c0] using (nb090_compact_fv_empty_0292 A)

theorem nb090_wpp_notmem_1017 (v : Var) : (nb090_alpha_dummy_384 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_384, fv_syn_c0] using (nb090_compact_fv_empty_0293 v)

theorem nb090_wpp_notmem_1018 (A : Class) : (nb090_alpha_dummy_381 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_381, fv_syn_c0] using (nb090_compact_fv_empty_0294 A)

theorem nb090_wpp_notmem_1019 (v : Var) : (nb090_alpha_dummy_383 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_383, fv_syn_c0] using (nb090_compact_fv_empty_0295 v)

theorem nb090_wpp_notmem_1020 (A : Class) : (nb090_alpha_dummy_387 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_387, fv_syn_c0] using (nb090_compact_fv_empty_0296 A)

theorem nb090_wpp_notmem_1021 (v : Var) : (nb090_alpha_dummy_388 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_388, fv_syn_c0] using (nb090_compact_fv_empty_0297 v)

theorem nb090_wpp_notmem_1022 (A : Class) : (nb090_alpha_dummy_385 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_385, fv_syn_c0] using (nb090_compact_fv_empty_0298 A)

theorem nb090_wpp_notmem_1023 (v : Var) : (nb090_alpha_dummy_386 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_386, fv_syn_c0] using (nb090_compact_fv_empty_0299 v)

theorem nb090_wpp_notmem_1024 (A : Class) : (nb090_alpha_dummy_373 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_373, fv_syn_c0] using (nb090_compact_fv_empty_0300 A)

theorem nb090_wpp_notmem_1025 (v : Var) : (nb090_alpha_dummy_374 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_374, fv_syn_c0] using (nb090_compact_fv_empty_0301 v)

theorem nb090_wpp_notmem_1026 (A : Class) : (nb090_alpha_dummy_375 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_375, fv_syn_c0] using (nb090_compact_fv_empty_0302 A)

theorem nb090_wpp_notmem_1027 (v : Var) : (nb090_alpha_dummy_376 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_376, fv_syn_c0] using (nb090_compact_fv_empty_0303 v)

theorem nb090_wpp_notmem_1028 (A : Class) : (nb090_alpha_dummy_378 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_378, fv_syn_c0] using (nb090_compact_fv_empty_0304 A)

theorem nb090_wpp_notmem_1029 (v : Var) : (nb090_alpha_dummy_380 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_380, fv_syn_c0] using (nb090_compact_fv_empty_0305 v)

theorem nb090_wpp_notmem_1030 (A : Class) : (nb090_alpha_dummy_377 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_377, fv_syn_c0] using (nb090_compact_fv_empty_0306 A)

theorem nb090_wpp_notmem_1031 (v : Var) : (nb090_alpha_dummy_379 v) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_379, fv_syn_c0] using (nb090_compact_fv_empty_0307 v)

theorem nb090_compact_envfresh_0118 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_397 A), (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A), (nb090_alpha_dummy_399 v)), ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)), ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)), ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)), ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_397 A) (nb090_alpha_dummy_400 v) (nb090_wpp_notmem_1004 A) (nb090_wpp_notmem_1005 v) (TEnvFresh.consFresh (nb090_alpha_dummy_396 A) (nb090_alpha_dummy_399 v) (nb090_wpp_notmem_1006 A) (nb090_wpp_notmem_1007 v) (TEnvFresh.consFresh (nb090_alpha_dummy_395 A) (nb090_alpha_dummy_398 v) (nb090_wpp_notmem_1008 A) (nb090_wpp_notmem_1009 v) (TEnvFresh.consFresh (nb090_alpha_dummy_393 A) (nb090_alpha_dummy_394 v) (nb090_wpp_notmem_1010 A) (nb090_wpp_notmem_1011 v) (TEnvFresh.consFresh (nb090_alpha_dummy_389 A) (nb090_alpha_dummy_391 v) (nb090_wpp_notmem_1012 A) (nb090_wpp_notmem_1013 v) (TEnvFresh.consFresh (nb090_alpha_dummy_390 A) (nb090_alpha_dummy_392 v) (nb090_wpp_notmem_1014 A) (nb090_wpp_notmem_1015 v) (TEnvFresh.consFresh (nb090_alpha_dummy_382 A) (nb090_alpha_dummy_384 v) (nb090_wpp_notmem_1016 A) (nb090_wpp_notmem_1017 v) (TEnvFresh.consFresh (nb090_alpha_dummy_381 A) (nb090_alpha_dummy_383 v) (nb090_wpp_notmem_1018 A) (nb090_wpp_notmem_1019 v) (TEnvFresh.consFresh (nb090_alpha_dummy_387 A) (nb090_alpha_dummy_388 v) (nb090_wpp_notmem_1020 A) (nb090_wpp_notmem_1021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_385 A) (nb090_alpha_dummy_386 v) (nb090_wpp_notmem_1022 A) (nb090_wpp_notmem_1023 v) (TEnvFresh.consFresh (nb090_alpha_dummy_373 A) (nb090_alpha_dummy_374 v) (nb090_wpp_notmem_1024 A) (nb090_wpp_notmem_1025 v) (TEnvFresh.consFresh (nb090_alpha_dummy_375 A) (nb090_alpha_dummy_376 v) (nb090_wpp_notmem_1026 A) (nb090_wpp_notmem_1027 v) (TEnvFresh.consFresh (nb090_alpha_dummy_378 A) (nb090_alpha_dummy_380 v) (nb090_wpp_notmem_1028 A) (nb090_wpp_notmem_1029 v) (TEnvFresh.consFresh (nb090_alpha_dummy_377 A) (nb090_alpha_dummy_379 v) (nb090_wpp_notmem_1030 A) (nb090_wpp_notmem_1031 v) (TEnvFresh.consFresh (nb090_alpha_dummy_331 A) (nb090_alpha_dummy_332 v h) (nb090_wpp_notmem_0914 A) (nb090_wpp_notmem_0915 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_329 A) (nb090_alpha_dummy_330 v h) (nb090_wpp_notmem_0916 A) (nb090_wpp_notmem_0917 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb090_wpp_refl_0118 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_397 A), (nb090_alpha_dummy_400 v)), ((nb090_alpha_dummy_396 A), (nb090_alpha_dummy_399 v)), ((nb090_alpha_dummy_395 A), (nb090_alpha_dummy_398 v)), ((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)), ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)), ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0118 v u A h)

theorem nb090_wpp_notmem_1032 (A : Class) : (nb090_alpha_dummy_393 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_393, fv_syn_cnnc] using (nb090_compact_fv_empty_0286 A)

theorem nb090_wpp_notmem_1033 (v : Var) : (nb090_alpha_dummy_394 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_394, fv_syn_cnnc] using (nb090_compact_fv_empty_0287 v)

theorem nb090_wpp_notmem_1034 (A : Class) : (nb090_alpha_dummy_389 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_389, fv_syn_cnnc] using (nb090_compact_fv_empty_0288 A)

theorem nb090_wpp_notmem_1035 (v : Var) : (nb090_alpha_dummy_391 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_391, fv_syn_cnnc] using (nb090_compact_fv_empty_0289 v)

theorem nb090_wpp_notmem_1036 (A : Class) : (nb090_alpha_dummy_390 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_390, fv_syn_cnnc] using (nb090_compact_fv_empty_0290 A)

theorem nb090_wpp_notmem_1037 (v : Var) : (nb090_alpha_dummy_392 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_392, fv_syn_cnnc] using (nb090_compact_fv_empty_0291 v)

theorem nb090_wpp_notmem_1038 (A : Class) : (nb090_alpha_dummy_382 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_382, fv_syn_cnnc] using (nb090_compact_fv_empty_0292 A)

theorem nb090_wpp_notmem_1039 (v : Var) : (nb090_alpha_dummy_384 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_384, fv_syn_cnnc] using (nb090_compact_fv_empty_0293 v)

theorem nb090_wpp_notmem_1040 (A : Class) : (nb090_alpha_dummy_381 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_381, fv_syn_cnnc] using (nb090_compact_fv_empty_0294 A)

theorem nb090_wpp_notmem_1041 (v : Var) : (nb090_alpha_dummy_383 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_383, fv_syn_cnnc] using (nb090_compact_fv_empty_0295 v)

theorem nb090_wpp_notmem_1042 (A : Class) : (nb090_alpha_dummy_387 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_387, fv_syn_cnnc] using (nb090_compact_fv_empty_0296 A)

theorem nb090_wpp_notmem_1043 (v : Var) : (nb090_alpha_dummy_388 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_388, fv_syn_cnnc] using (nb090_compact_fv_empty_0297 v)

theorem nb090_wpp_notmem_1044 (A : Class) : (nb090_alpha_dummy_385 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_385, fv_syn_cnnc] using (nb090_compact_fv_empty_0298 A)

theorem nb090_wpp_notmem_1045 (v : Var) : (nb090_alpha_dummy_386 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_386, fv_syn_cnnc] using (nb090_compact_fv_empty_0299 v)

theorem nb090_wpp_notmem_1046 (A : Class) : (nb090_alpha_dummy_373 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_373, fv_syn_cnnc] using (nb090_compact_fv_empty_0300 A)

theorem nb090_wpp_notmem_1047 (v : Var) : (nb090_alpha_dummy_374 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_374, fv_syn_cnnc] using (nb090_compact_fv_empty_0301 v)

theorem nb090_wpp_notmem_1048 (A : Class) : (nb090_alpha_dummy_375 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_375, fv_syn_cnnc] using (nb090_compact_fv_empty_0302 A)

theorem nb090_wpp_notmem_1049 (v : Var) : (nb090_alpha_dummy_376 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_376, fv_syn_cnnc] using (nb090_compact_fv_empty_0303 v)

theorem nb090_wpp_notmem_1050 (A : Class) : (nb090_alpha_dummy_378 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_378, fv_syn_cnnc] using (nb090_compact_fv_empty_0304 A)

theorem nb090_wpp_notmem_1051 (v : Var) : (nb090_alpha_dummy_380 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_380, fv_syn_cnnc] using (nb090_compact_fv_empty_0305 v)

theorem nb090_wpp_notmem_1052 (A : Class) : (nb090_alpha_dummy_377 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_377, fv_syn_cnnc] using (nb090_compact_fv_empty_0306 A)

theorem nb090_wpp_notmem_1053 (v : Var) : (nb090_alpha_dummy_379 v) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_379, fv_syn_cnnc] using (nb090_compact_fv_empty_0307 v)

theorem nb090_compact_envfresh_0119 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)), ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)), ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_393 A) (nb090_alpha_dummy_394 v) (nb090_wpp_notmem_1032 A) (nb090_wpp_notmem_1033 v) (TEnvFresh.consFresh (nb090_alpha_dummy_389 A) (nb090_alpha_dummy_391 v) (nb090_wpp_notmem_1034 A) (nb090_wpp_notmem_1035 v) (TEnvFresh.consFresh (nb090_alpha_dummy_390 A) (nb090_alpha_dummy_392 v) (nb090_wpp_notmem_1036 A) (nb090_wpp_notmem_1037 v) (TEnvFresh.consFresh (nb090_alpha_dummy_382 A) (nb090_alpha_dummy_384 v) (nb090_wpp_notmem_1038 A) (nb090_wpp_notmem_1039 v) (TEnvFresh.consFresh (nb090_alpha_dummy_381 A) (nb090_alpha_dummy_383 v) (nb090_wpp_notmem_1040 A) (nb090_wpp_notmem_1041 v) (TEnvFresh.consFresh (nb090_alpha_dummy_387 A) (nb090_alpha_dummy_388 v) (nb090_wpp_notmem_1042 A) (nb090_wpp_notmem_1043 v) (TEnvFresh.consFresh (nb090_alpha_dummy_385 A) (nb090_alpha_dummy_386 v) (nb090_wpp_notmem_1044 A) (nb090_wpp_notmem_1045 v) (TEnvFresh.consFresh (nb090_alpha_dummy_373 A) (nb090_alpha_dummy_374 v) (nb090_wpp_notmem_1046 A) (nb090_wpp_notmem_1047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_375 A) (nb090_alpha_dummy_376 v) (nb090_wpp_notmem_1048 A) (nb090_wpp_notmem_1049 v) (TEnvFresh.consFresh (nb090_alpha_dummy_378 A) (nb090_alpha_dummy_380 v) (nb090_wpp_notmem_1050 A) (nb090_wpp_notmem_1051 v) (TEnvFresh.consFresh (nb090_alpha_dummy_377 A) (nb090_alpha_dummy_379 v) (nb090_wpp_notmem_1052 A) (nb090_wpp_notmem_1053 v) (TEnvFresh.consFresh (nb090_alpha_dummy_331 A) (nb090_alpha_dummy_332 v h) (nb090_wpp_notmem_0936 A) (nb090_wpp_notmem_0937 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_329 A) (nb090_alpha_dummy_330 v h) (nb090_wpp_notmem_0938 A) (nb090_wpp_notmem_0939 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb090_wpp_refl_0119 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_393 A), (nb090_alpha_dummy_394 v)), ((nb090_alpha_dummy_389 A), (nb090_alpha_dummy_391 v)), ((nb090_alpha_dummy_390 A), (nb090_alpha_dummy_392 v)), ((nb090_alpha_dummy_382 A), (nb090_alpha_dummy_384 v)), ((nb090_alpha_dummy_381 A), (nb090_alpha_dummy_383 v)), ((nb090_alpha_dummy_387 A), (nb090_alpha_dummy_388 v)), ((nb090_alpha_dummy_385 A), (nb090_alpha_dummy_386 v)), ((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)), ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)), ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)), ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0119 v u A h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
