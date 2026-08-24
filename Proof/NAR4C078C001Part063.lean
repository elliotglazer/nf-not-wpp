import NAR4C078C001Part062

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

noncomputable def nb078_split_alpha_0033 (x : Var) (y : Var) (g : Var) : TAlphaWff [((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.classMem (Class.cv (nb078_alpha_dummy_363)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_332))))) (Wff.classMem (Class.cv (nb078_alpha_dummy_364 g)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0338) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0339 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0338) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0339 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0368) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0369 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0366) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0367 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_332))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_334 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0342) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0343 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0342) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0343 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0340) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0341 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346), (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)), ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0111 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0346) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0347 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0344) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0345 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0350) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0351 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0348) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0349 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0346) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0347 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0344) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0345 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0350) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0351 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0348) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0349 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346), (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)), ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0112 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0354) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0355 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0352) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0353 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0354) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0355 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0352) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0353 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0358) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0359 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0356) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0357 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0358) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0359 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0356) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0357 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0340) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0341 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0113 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0340) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0341 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0340) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0341 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0113 x y g)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0338) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0339 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0338) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0339 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0368) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0369 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0366) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0367 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_332))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_334 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0342) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0343 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0342) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0343 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0340) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0341 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346), (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)), ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0111 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0346) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0347 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0344) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0345 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0350) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0351 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0348) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0349 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0346) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0347 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0344) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0345 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0350) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0351 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0348) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0349 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346), (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)), ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0112 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0354) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0355 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0352) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0353 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0354) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0355 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0352) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0353 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_339))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_341 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0358) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0359 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0356) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0357 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0358) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0359 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0356) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0357 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0340) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0341 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0113 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0340) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0341 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0340) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0341 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_365), (nb078_alpha_dummy_366 g)), ((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0113 x y g))))))))))))))))))))))))

theorem nb078_wpp_notmem_0934 : (nb078_alpha_dummy_363) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_363, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0276)

theorem nb078_wpp_notmem_0935 (g : Var) : (nb078_alpha_dummy_364 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_364, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0277 g)

theorem nb078_wpp_notmem_0936 : (nb078_alpha_dummy_332) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_332, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0264)

theorem nb078_wpp_notmem_0937 (g : Var) : (nb078_alpha_dummy_334 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_334, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0265 g)

theorem nb078_wpp_notmem_0938 : (nb078_alpha_dummy_331) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_331, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0266)

theorem nb078_wpp_notmem_0939 (g : Var) : (nb078_alpha_dummy_333 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_333, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0267 g)

theorem nb078_wpp_notmem_0940 : (nb078_alpha_dummy_361) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_361, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0278)

theorem nb078_wpp_notmem_0941 (g : Var) : (nb078_alpha_dummy_362 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_362, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0279 g)

theorem nb078_wpp_notmem_0942 : (nb078_alpha_dummy_335) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_335, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0270)

theorem nb078_wpp_notmem_0943 (g : Var) : (nb078_alpha_dummy_336 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_336, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0271 g)

theorem nb078_wpp_notmem_0944 : (nb078_alpha_dummy_289) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_289, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0272)

theorem nb078_wpp_notmem_0945 (g : Var) : (nb078_alpha_dummy_292 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_292, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0273 g)

theorem nb078_compact_envfresh_0114 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_363) (nb078_alpha_dummy_364 g) (nb078_wpp_notmem_0934) (nb078_wpp_notmem_0935 g) (TEnvFresh.consFresh (nb078_alpha_dummy_332) (nb078_alpha_dummy_334 g) (nb078_wpp_notmem_0936) (nb078_wpp_notmem_0937 g) (TEnvFresh.consFresh (nb078_alpha_dummy_331) (nb078_alpha_dummy_333 g) (nb078_wpp_notmem_0938) (nb078_wpp_notmem_0939 g) (TEnvFresh.consFresh (nb078_alpha_dummy_361) (nb078_alpha_dummy_362 g) (nb078_wpp_notmem_0940) (nb078_wpp_notmem_0941 g) (TEnvFresh.consFresh (nb078_alpha_dummy_335) (nb078_alpha_dummy_336 g) (nb078_wpp_notmem_0942) (nb078_wpp_notmem_0943 g) (TEnvFresh.consFresh (nb078_alpha_dummy_289) (nb078_alpha_dummy_292 g) (nb078_wpp_notmem_0944) (nb078_wpp_notmem_0945 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0844) (nb078_wpp_notmem_0845 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0846) (nb078_wpp_notmem_0847 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0848) (nb078_wpp_notmem_0849 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0850) (nb078_wpp_notmem_0851 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0852) (nb078_wpp_notmem_0853 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0854) (nb078_wpp_notmem_0855 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb078_wpp_refl_0114 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0114 x y g)

theorem nb078_compact_fv_empty_0280 : (nb078_alpha_dummy_389) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0946 : (nb078_alpha_dummy_389) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_389, fv_syn_c1c] using (nb078_compact_fv_empty_0280)

theorem nb078_compact_fv_empty_0281 (g : Var) : (nb078_alpha_dummy_392 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0947 (g : Var) : (nb078_alpha_dummy_392 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_392, fv_syn_c1c] using (nb078_compact_fv_empty_0281 g)

theorem nb078_compact_fv_empty_0282 : (nb078_alpha_dummy_388) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0948 : (nb078_alpha_dummy_388) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_388, fv_syn_c1c] using (nb078_compact_fv_empty_0282)

theorem nb078_compact_fv_empty_0283 (g : Var) : (nb078_alpha_dummy_391 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0949 (g : Var) : (nb078_alpha_dummy_391 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_391, fv_syn_c1c] using (nb078_compact_fv_empty_0283 g)

theorem nb078_compact_fv_empty_0284 : (nb078_alpha_dummy_387) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0950 : (nb078_alpha_dummy_387) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_387, fv_syn_c1c] using (nb078_compact_fv_empty_0284)

theorem nb078_compact_fv_empty_0285 (g : Var) : (nb078_alpha_dummy_390 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0951 (g : Var) : (nb078_alpha_dummy_390 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_390, fv_syn_c1c] using (nb078_compact_fv_empty_0285 g)

theorem nb078_compact_fv_empty_0286 : (nb078_alpha_dummy_385) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0952 : (nb078_alpha_dummy_385) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_385, fv_syn_c1c] using (nb078_compact_fv_empty_0286)

theorem nb078_compact_fv_empty_0287 (g : Var) : (nb078_alpha_dummy_386 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0953 (g : Var) : (nb078_alpha_dummy_386 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_386, fv_syn_c1c] using (nb078_compact_fv_empty_0287 g)

theorem nb078_compact_fv_empty_0288 : (nb078_alpha_dummy_381) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0954 : (nb078_alpha_dummy_381) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_381, fv_syn_c1c] using (nb078_compact_fv_empty_0288)

theorem nb078_compact_fv_empty_0289 (g : Var) : (nb078_alpha_dummy_383 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0955 (g : Var) : (nb078_alpha_dummy_383 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_383, fv_syn_c1c] using (nb078_compact_fv_empty_0289 g)

theorem nb078_compact_fv_empty_0290 : (nb078_alpha_dummy_382) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0956 : (nb078_alpha_dummy_382) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_382, fv_syn_c1c] using (nb078_compact_fv_empty_0290)

theorem nb078_compact_fv_empty_0291 (g : Var) : (nb078_alpha_dummy_384 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0957 (g : Var) : (nb078_alpha_dummy_384 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_384, fv_syn_c1c] using (nb078_compact_fv_empty_0291 g)

theorem nb078_compact_fv_empty_0292 : (nb078_alpha_dummy_374) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0958 : (nb078_alpha_dummy_374) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_374, fv_syn_c1c] using (nb078_compact_fv_empty_0292)

theorem nb078_compact_fv_empty_0293 (g : Var) : (nb078_alpha_dummy_376 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0959 (g : Var) : (nb078_alpha_dummy_376 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_376, fv_syn_c1c] using (nb078_compact_fv_empty_0293 g)

theorem nb078_compact_fv_empty_0294 : (nb078_alpha_dummy_373) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0960 : (nb078_alpha_dummy_373) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_373, fv_syn_c1c] using (nb078_compact_fv_empty_0294)

theorem nb078_compact_fv_empty_0295 (g : Var) : (nb078_alpha_dummy_375 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0961 (g : Var) : (nb078_alpha_dummy_375 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_375, fv_syn_c1c] using (nb078_compact_fv_empty_0295 g)

theorem nb078_compact_fv_empty_0296 : (nb078_alpha_dummy_379) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0962 : (nb078_alpha_dummy_379) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_379, fv_syn_c1c] using (nb078_compact_fv_empty_0296)

theorem nb078_compact_fv_empty_0297 (g : Var) : (nb078_alpha_dummy_380 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0963 (g : Var) : (nb078_alpha_dummy_380 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_380, fv_syn_c1c] using (nb078_compact_fv_empty_0297 g)

theorem nb078_compact_fv_empty_0298 : (nb078_alpha_dummy_377) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0964 : (nb078_alpha_dummy_377) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_377, fv_syn_c1c] using (nb078_compact_fv_empty_0298)

theorem nb078_compact_fv_empty_0299 (g : Var) : (nb078_alpha_dummy_378 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0965 (g : Var) : (nb078_alpha_dummy_378 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_378, fv_syn_c1c] using (nb078_compact_fv_empty_0299 g)

theorem nb078_compact_fv_empty_0300 : (nb078_alpha_dummy_368) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0966 : (nb078_alpha_dummy_368) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_368, fv_syn_c1c] using (nb078_compact_fv_empty_0300)

theorem nb078_compact_fv_empty_0301 (g : Var) : (nb078_alpha_dummy_370 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0967 (g : Var) : (nb078_alpha_dummy_370 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_370, fv_syn_c1c] using (nb078_compact_fv_empty_0301 g)

theorem nb078_compact_fv_empty_0302 : (nb078_alpha_dummy_367) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0968 : (nb078_alpha_dummy_367) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_367, fv_syn_c1c] using (nb078_compact_fv_empty_0302)

theorem nb078_compact_fv_empty_0303 (g : Var) : (nb078_alpha_dummy_369 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0969 (g : Var) : (nb078_alpha_dummy_369 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_369, fv_syn_c1c] using (nb078_compact_fv_empty_0303 g)

theorem nb078_compact_fv_empty_0304 : (nb078_alpha_dummy_371) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0970 : (nb078_alpha_dummy_371) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_371, fv_syn_c1c] using (nb078_compact_fv_empty_0304)

theorem nb078_compact_fv_empty_0305 (g : Var) : (nb078_alpha_dummy_372 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0971 (g : Var) : (nb078_alpha_dummy_372 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_372, fv_syn_c1c] using (nb078_compact_fv_empty_0305 g)

theorem nb078_compact_envfresh_0115 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388), (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)), ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)), ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)), ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_389) (nb078_alpha_dummy_392 g) (nb078_wpp_notmem_0946) (nb078_wpp_notmem_0947 g) (TEnvFresh.consFresh (nb078_alpha_dummy_388) (nb078_alpha_dummy_391 g) (nb078_wpp_notmem_0948) (nb078_wpp_notmem_0949 g) (TEnvFresh.consFresh (nb078_alpha_dummy_387) (nb078_alpha_dummy_390 g) (nb078_wpp_notmem_0950) (nb078_wpp_notmem_0951 g) (TEnvFresh.consFresh (nb078_alpha_dummy_385) (nb078_alpha_dummy_386 g) (nb078_wpp_notmem_0952) (nb078_wpp_notmem_0953 g) (TEnvFresh.consFresh (nb078_alpha_dummy_381) (nb078_alpha_dummy_383 g) (nb078_wpp_notmem_0954) (nb078_wpp_notmem_0955 g) (TEnvFresh.consFresh (nb078_alpha_dummy_382) (nb078_alpha_dummy_384 g) (nb078_wpp_notmem_0956) (nb078_wpp_notmem_0957 g) (TEnvFresh.consFresh (nb078_alpha_dummy_374) (nb078_alpha_dummy_376 g) (nb078_wpp_notmem_0958) (nb078_wpp_notmem_0959 g) (TEnvFresh.consFresh (nb078_alpha_dummy_373) (nb078_alpha_dummy_375 g) (nb078_wpp_notmem_0960) (nb078_wpp_notmem_0961 g) (TEnvFresh.consFresh (nb078_alpha_dummy_379) (nb078_alpha_dummy_380 g) (nb078_wpp_notmem_0962) (nb078_wpp_notmem_0963 g) (TEnvFresh.consFresh (nb078_alpha_dummy_377) (nb078_alpha_dummy_378 g) (nb078_wpp_notmem_0964) (nb078_wpp_notmem_0965 g) (TEnvFresh.consFresh (nb078_alpha_dummy_368) (nb078_alpha_dummy_370 g) (nb078_wpp_notmem_0966) (nb078_wpp_notmem_0967 g) (TEnvFresh.consFresh (nb078_alpha_dummy_367) (nb078_alpha_dummy_369 g) (nb078_wpp_notmem_0968) (nb078_wpp_notmem_0969 g) (TEnvFresh.consFresh (nb078_alpha_dummy_371) (nb078_alpha_dummy_372 g) (nb078_wpp_notmem_0970) (nb078_wpp_notmem_0971 g) (TEnvFresh.consFresh (nb078_alpha_dummy_289) (nb078_alpha_dummy_292 g) (nb078_wpp_notmem_0876) (nb078_wpp_notmem_0877 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0746) (nb078_wpp_notmem_0747 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0748) (nb078_wpp_notmem_0749 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0750) (nb078_wpp_notmem_0751 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0752) (nb078_wpp_notmem_0753 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0754) (nb078_wpp_notmem_0755 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0115 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388), (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)), ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)), ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)), ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0115 x y g)

theorem nb078_wpp_notmem_0972 : (nb078_alpha_dummy_389) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_389, fv_syn_c0] using (nb078_compact_fv_empty_0280)

theorem nb078_wpp_notmem_0973 (g : Var) : (nb078_alpha_dummy_392 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_392, fv_syn_c0] using (nb078_compact_fv_empty_0281 g)

theorem nb078_wpp_notmem_0974 : (nb078_alpha_dummy_388) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_388, fv_syn_c0] using (nb078_compact_fv_empty_0282)

theorem nb078_wpp_notmem_0975 (g : Var) : (nb078_alpha_dummy_391 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_391, fv_syn_c0] using (nb078_compact_fv_empty_0283 g)

theorem nb078_wpp_notmem_0976 : (nb078_alpha_dummy_387) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_387, fv_syn_c0] using (nb078_compact_fv_empty_0284)

theorem nb078_wpp_notmem_0977 (g : Var) : (nb078_alpha_dummy_390 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_390, fv_syn_c0] using (nb078_compact_fv_empty_0285 g)

theorem nb078_wpp_notmem_0978 : (nb078_alpha_dummy_385) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_385, fv_syn_c0] using (nb078_compact_fv_empty_0286)

theorem nb078_wpp_notmem_0979 (g : Var) : (nb078_alpha_dummy_386 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_386, fv_syn_c0] using (nb078_compact_fv_empty_0287 g)

theorem nb078_wpp_notmem_0980 : (nb078_alpha_dummy_381) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_381, fv_syn_c0] using (nb078_compact_fv_empty_0288)

theorem nb078_wpp_notmem_0981 (g : Var) : (nb078_alpha_dummy_383 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_383, fv_syn_c0] using (nb078_compact_fv_empty_0289 g)

theorem nb078_wpp_notmem_0982 : (nb078_alpha_dummy_382) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_382, fv_syn_c0] using (nb078_compact_fv_empty_0290)

theorem nb078_wpp_notmem_0983 (g : Var) : (nb078_alpha_dummy_384 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_384, fv_syn_c0] using (nb078_compact_fv_empty_0291 g)

theorem nb078_wpp_notmem_0984 : (nb078_alpha_dummy_374) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_374, fv_syn_c0] using (nb078_compact_fv_empty_0292)

theorem nb078_wpp_notmem_0985 (g : Var) : (nb078_alpha_dummy_376 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_376, fv_syn_c0] using (nb078_compact_fv_empty_0293 g)

theorem nb078_wpp_notmem_0986 : (nb078_alpha_dummy_373) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_373, fv_syn_c0] using (nb078_compact_fv_empty_0294)

theorem nb078_wpp_notmem_0987 (g : Var) : (nb078_alpha_dummy_375 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_375, fv_syn_c0] using (nb078_compact_fv_empty_0295 g)

theorem nb078_wpp_notmem_0988 : (nb078_alpha_dummy_379) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_379, fv_syn_c0] using (nb078_compact_fv_empty_0296)

theorem nb078_wpp_notmem_0989 (g : Var) : (nb078_alpha_dummy_380 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_380, fv_syn_c0] using (nb078_compact_fv_empty_0297 g)

theorem nb078_wpp_notmem_0990 : (nb078_alpha_dummy_377) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_377, fv_syn_c0] using (nb078_compact_fv_empty_0298)

theorem nb078_wpp_notmem_0991 (g : Var) : (nb078_alpha_dummy_378 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_378, fv_syn_c0] using (nb078_compact_fv_empty_0299 g)

theorem nb078_wpp_notmem_0992 : (nb078_alpha_dummy_368) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_368, fv_syn_c0] using (nb078_compact_fv_empty_0300)

theorem nb078_wpp_notmem_0993 (g : Var) : (nb078_alpha_dummy_370 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_370, fv_syn_c0] using (nb078_compact_fv_empty_0301 g)

theorem nb078_wpp_notmem_0994 : (nb078_alpha_dummy_367) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_367, fv_syn_c0] using (nb078_compact_fv_empty_0302)

theorem nb078_wpp_notmem_0995 (g : Var) : (nb078_alpha_dummy_369 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_369, fv_syn_c0] using (nb078_compact_fv_empty_0303 g)

theorem nb078_wpp_notmem_0996 : (nb078_alpha_dummy_371) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_371, fv_syn_c0] using (nb078_compact_fv_empty_0304)

theorem nb078_wpp_notmem_0997 (g : Var) : (nb078_alpha_dummy_372 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_372, fv_syn_c0] using (nb078_compact_fv_empty_0305 g)

theorem nb078_compact_envfresh_0116 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388), (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)), ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)), ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)), ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_389) (nb078_alpha_dummy_392 g) (nb078_wpp_notmem_0972) (nb078_wpp_notmem_0973 g) (TEnvFresh.consFresh (nb078_alpha_dummy_388) (nb078_alpha_dummy_391 g) (nb078_wpp_notmem_0974) (nb078_wpp_notmem_0975 g) (TEnvFresh.consFresh (nb078_alpha_dummy_387) (nb078_alpha_dummy_390 g) (nb078_wpp_notmem_0976) (nb078_wpp_notmem_0977 g) (TEnvFresh.consFresh (nb078_alpha_dummy_385) (nb078_alpha_dummy_386 g) (nb078_wpp_notmem_0978) (nb078_wpp_notmem_0979 g) (TEnvFresh.consFresh (nb078_alpha_dummy_381) (nb078_alpha_dummy_383 g) (nb078_wpp_notmem_0980) (nb078_wpp_notmem_0981 g) (TEnvFresh.consFresh (nb078_alpha_dummy_382) (nb078_alpha_dummy_384 g) (nb078_wpp_notmem_0982) (nb078_wpp_notmem_0983 g) (TEnvFresh.consFresh (nb078_alpha_dummy_374) (nb078_alpha_dummy_376 g) (nb078_wpp_notmem_0984) (nb078_wpp_notmem_0985 g) (TEnvFresh.consFresh (nb078_alpha_dummy_373) (nb078_alpha_dummy_375 g) (nb078_wpp_notmem_0986) (nb078_wpp_notmem_0987 g) (TEnvFresh.consFresh (nb078_alpha_dummy_379) (nb078_alpha_dummy_380 g) (nb078_wpp_notmem_0988) (nb078_wpp_notmem_0989 g) (TEnvFresh.consFresh (nb078_alpha_dummy_377) (nb078_alpha_dummy_378 g) (nb078_wpp_notmem_0990) (nb078_wpp_notmem_0991 g) (TEnvFresh.consFresh (nb078_alpha_dummy_368) (nb078_alpha_dummy_370 g) (nb078_wpp_notmem_0992) (nb078_wpp_notmem_0993 g) (TEnvFresh.consFresh (nb078_alpha_dummy_367) (nb078_alpha_dummy_369 g) (nb078_wpp_notmem_0994) (nb078_wpp_notmem_0995 g) (TEnvFresh.consFresh (nb078_alpha_dummy_371) (nb078_alpha_dummy_372 g) (nb078_wpp_notmem_0996) (nb078_wpp_notmem_0997 g) (TEnvFresh.consFresh (nb078_alpha_dummy_289) (nb078_alpha_dummy_292 g) (nb078_wpp_notmem_0898) (nb078_wpp_notmem_0899 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0778) (nb078_wpp_notmem_0779 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0780) (nb078_wpp_notmem_0781 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0782) (nb078_wpp_notmem_0783 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0784) (nb078_wpp_notmem_0785 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0786) (nb078_wpp_notmem_0787 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0788) (nb078_wpp_notmem_0789 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0116 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388), (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)), ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)), ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)), ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0116 x y g)

theorem nb078_wpp_notmem_0998 : (nb078_alpha_dummy_385) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_385, fv_syn_cnnc] using (nb078_compact_fv_empty_0286)

theorem nb078_wpp_notmem_0999 (g : Var) : (nb078_alpha_dummy_386 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_386, fv_syn_cnnc] using (nb078_compact_fv_empty_0287 g)

theorem nb078_wpp_notmem_1000 : (nb078_alpha_dummy_381) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_381, fv_syn_cnnc] using (nb078_compact_fv_empty_0288)

theorem nb078_wpp_notmem_1001 (g : Var) : (nb078_alpha_dummy_383 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_383, fv_syn_cnnc] using (nb078_compact_fv_empty_0289 g)

theorem nb078_wpp_notmem_1002 : (nb078_alpha_dummy_382) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_382, fv_syn_cnnc] using (nb078_compact_fv_empty_0290)

theorem nb078_wpp_notmem_1003 (g : Var) : (nb078_alpha_dummy_384 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_384, fv_syn_cnnc] using (nb078_compact_fv_empty_0291 g)

theorem nb078_wpp_notmem_1004 : (nb078_alpha_dummy_374) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_374, fv_syn_cnnc] using (nb078_compact_fv_empty_0292)

theorem nb078_wpp_notmem_1005 (g : Var) : (nb078_alpha_dummy_376 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_376, fv_syn_cnnc] using (nb078_compact_fv_empty_0293 g)

theorem nb078_wpp_notmem_1006 : (nb078_alpha_dummy_373) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_373, fv_syn_cnnc] using (nb078_compact_fv_empty_0294)

theorem nb078_wpp_notmem_1007 (g : Var) : (nb078_alpha_dummy_375 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_375, fv_syn_cnnc] using (nb078_compact_fv_empty_0295 g)

theorem nb078_wpp_notmem_1008 : (nb078_alpha_dummy_379) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_379, fv_syn_cnnc] using (nb078_compact_fv_empty_0296)

theorem nb078_wpp_notmem_1009 (g : Var) : (nb078_alpha_dummy_380 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_380, fv_syn_cnnc] using (nb078_compact_fv_empty_0297 g)

theorem nb078_wpp_notmem_1010 : (nb078_alpha_dummy_377) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_377, fv_syn_cnnc] using (nb078_compact_fv_empty_0298)

theorem nb078_wpp_notmem_1011 (g : Var) : (nb078_alpha_dummy_378 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_378, fv_syn_cnnc] using (nb078_compact_fv_empty_0299 g)

theorem nb078_wpp_notmem_1012 : (nb078_alpha_dummy_368) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_368, fv_syn_cnnc] using (nb078_compact_fv_empty_0300)

theorem nb078_wpp_notmem_1013 (g : Var) : (nb078_alpha_dummy_370 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_370, fv_syn_cnnc] using (nb078_compact_fv_empty_0301 g)

theorem nb078_wpp_notmem_1014 : (nb078_alpha_dummy_367) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_367, fv_syn_cnnc] using (nb078_compact_fv_empty_0302)

theorem nb078_wpp_notmem_1015 (g : Var) : (nb078_alpha_dummy_369 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_369, fv_syn_cnnc] using (nb078_compact_fv_empty_0303 g)

theorem nb078_wpp_notmem_1016 : (nb078_alpha_dummy_371) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_371, fv_syn_cnnc] using (nb078_compact_fv_empty_0304)

theorem nb078_wpp_notmem_1017 (g : Var) : (nb078_alpha_dummy_372 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_372, fv_syn_cnnc] using (nb078_compact_fv_empty_0305 g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
