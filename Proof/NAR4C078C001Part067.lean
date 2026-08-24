import NAR4C078C001Part066

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

noncomputable def nb078_split_alpha_0037 (x : Var) (y : Var) (g : Var) : TAlphaWff [((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_443)) (syn_cphi (Class.cv (nb078_alpha_dummy_410)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_443)) (syn_cphi (Class.cv (nb078_alpha_dummy_410)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_444 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_444 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0418) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0419 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0418) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0419 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0448) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0449 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0446) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0447 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_410))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_412 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0422) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0423 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0422) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0423 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0420) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0421 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_425), (nb078_alpha_dummy_428 g)), ((nb078_alpha_dummy_424), (nb078_alpha_dummy_427 g)), ((nb078_alpha_dummy_423), (nb078_alpha_dummy_426 g)), ((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)), ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)), ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)), ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0125 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0426) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0427 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0424) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0425 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0430) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0431 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0428) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0429 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0426) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0427 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0424) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0425 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0430) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0431 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0428) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0429 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_425), (nb078_alpha_dummy_428 g)), ((nb078_alpha_dummy_424), (nb078_alpha_dummy_427 g)), ((nb078_alpha_dummy_423), (nb078_alpha_dummy_426 g)), ((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)), ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)), ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)), ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0126 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0434) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0435 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0433 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0434) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0435 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0433 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0438) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0439 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0436) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0437 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0438) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0439 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0436) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0437 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0420) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0421 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)), ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)), ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)), ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0127 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0420) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0421 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0420) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0421 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)), ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)), ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)), ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0127 x y g)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0418) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0419 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0418) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0419 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0448) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0449 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0446) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0447 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_410))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_412 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0422) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0423 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0422) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0423 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0420) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0421 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_425), (nb078_alpha_dummy_428 g)), ((nb078_alpha_dummy_424), (nb078_alpha_dummy_427 g)), ((nb078_alpha_dummy_423), (nb078_alpha_dummy_426 g)), ((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)), ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)), ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)), ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0125 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0426) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0427 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0424) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0425 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0430) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0431 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0428) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0429 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0426) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0427 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0424) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0425 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0430) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0431 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0428) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0429 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_425), (nb078_alpha_dummy_428 g)), ((nb078_alpha_dummy_424), (nb078_alpha_dummy_427 g)), ((nb078_alpha_dummy_423), (nb078_alpha_dummy_426 g)), ((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)), ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)), ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)), ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0126 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0434) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0435 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0433 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0434) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0435 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0433 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0438) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0439 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0436) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0437 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0438) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0439 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0436) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0437 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0420) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0421 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)), ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)), ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)), ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0127 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0420) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0421 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0420) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0421 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)), ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)), ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)), ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0127 x y g))))))))))))))))))))

theorem nb078_wpp_notmem_1124 : (nb078_alpha_dummy_441) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_441, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0334)

theorem nb078_wpp_notmem_1125 (g : Var) : (nb078_alpha_dummy_442 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_442, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0335 g)

theorem nb078_wpp_notmem_1126 : (nb078_alpha_dummy_410) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_410, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0324)

theorem nb078_wpp_notmem_1127 (g : Var) : (nb078_alpha_dummy_412 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_412, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0325 g)

theorem nb078_wpp_notmem_1128 : (nb078_alpha_dummy_409) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_409, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0326)

theorem nb078_wpp_notmem_1129 (g : Var) : (nb078_alpha_dummy_411 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_411, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0327 g)

theorem nb078_wpp_notmem_1130 : (nb078_alpha_dummy_439) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_439, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0336)

theorem nb078_wpp_notmem_1131 (g : Var) : (nb078_alpha_dummy_440 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_440, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0337 g)

theorem nb078_wpp_notmem_1132 : (nb078_alpha_dummy_413) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_413, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0330)

theorem nb078_wpp_notmem_1133 (g : Var) : (nb078_alpha_dummy_414 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_414, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0331 g)

theorem nb078_compact_envfresh_0128 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_441) (nb078_alpha_dummy_442 g) (nb078_wpp_notmem_1124) (nb078_wpp_notmem_1125 g) (TEnvFresh.consFresh (nb078_alpha_dummy_410) (nb078_alpha_dummy_412 g) (nb078_wpp_notmem_1126) (nb078_wpp_notmem_1127 g) (TEnvFresh.consFresh (nb078_alpha_dummy_409) (nb078_alpha_dummy_411 g) (nb078_wpp_notmem_1128) (nb078_wpp_notmem_1129 g) (TEnvFresh.consFresh (nb078_alpha_dummy_439) (nb078_alpha_dummy_440 g) (nb078_wpp_notmem_1130) (nb078_wpp_notmem_1131 g) (TEnvFresh.consFresh (nb078_alpha_dummy_413) (nb078_alpha_dummy_414 g) (nb078_wpp_notmem_1132) (nb078_wpp_notmem_1133 g) (TEnvFresh.consFresh (nb078_alpha_dummy_368) (nb078_alpha_dummy_370 g) (nb078_wpp_notmem_1046) (nb078_wpp_notmem_1047 g) (TEnvFresh.consFresh (nb078_alpha_dummy_367) (nb078_alpha_dummy_369 g) (nb078_wpp_notmem_1048) (nb078_wpp_notmem_1049 g) (TEnvFresh.consFresh (nb078_alpha_dummy_371) (nb078_alpha_dummy_372 g) (nb078_wpp_notmem_1050) (nb078_wpp_notmem_1051 g) (TEnvFresh.consFresh (nb078_alpha_dummy_289) (nb078_alpha_dummy_292 g) (nb078_wpp_notmem_0944) (nb078_wpp_notmem_0945 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0844) (nb078_wpp_notmem_0845 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0846) (nb078_wpp_notmem_0847 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0848) (nb078_wpp_notmem_0849 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0850) (nb078_wpp_notmem_0851 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0852) (nb078_wpp_notmem_0853 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0854) (nb078_wpp_notmem_0855 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0128 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0128 x y g)

theorem nb078_compact_fv_empty_0338 : (nb078_alpha_dummy_461) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1134 : (nb078_alpha_dummy_461) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_461, fv_syn_c1c] using (nb078_compact_fv_empty_0338)

theorem nb078_compact_fv_empty_0339 (g : Var) : (nb078_alpha_dummy_464 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1135 (g : Var) : (nb078_alpha_dummy_464 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_464, fv_syn_c1c] using (nb078_compact_fv_empty_0339 g)

theorem nb078_compact_fv_empty_0340 : (nb078_alpha_dummy_460) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1136 : (nb078_alpha_dummy_460) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_460, fv_syn_c1c] using (nb078_compact_fv_empty_0340)

theorem nb078_compact_fv_empty_0341 (g : Var) : (nb078_alpha_dummy_463 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1137 (g : Var) : (nb078_alpha_dummy_463 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_463, fv_syn_c1c] using (nb078_compact_fv_empty_0341 g)

theorem nb078_compact_fv_empty_0342 : (nb078_alpha_dummy_459) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1138 : (nb078_alpha_dummy_459) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_459, fv_syn_c1c] using (nb078_compact_fv_empty_0342)

theorem nb078_compact_fv_empty_0343 (g : Var) : (nb078_alpha_dummy_462 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1139 (g : Var) : (nb078_alpha_dummy_462 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_462, fv_syn_c1c] using (nb078_compact_fv_empty_0343 g)

theorem nb078_compact_fv_empty_0344 : (nb078_alpha_dummy_457) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1140 : (nb078_alpha_dummy_457) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_457, fv_syn_c1c] using (nb078_compact_fv_empty_0344)

theorem nb078_compact_fv_empty_0345 (g : Var) : (nb078_alpha_dummy_458 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1141 (g : Var) : (nb078_alpha_dummy_458 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_458, fv_syn_c1c] using (nb078_compact_fv_empty_0345 g)

theorem nb078_compact_fv_empty_0346 : (nb078_alpha_dummy_453) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1142 : (nb078_alpha_dummy_453) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_453, fv_syn_c1c] using (nb078_compact_fv_empty_0346)

theorem nb078_compact_fv_empty_0347 (g : Var) : (nb078_alpha_dummy_455 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1143 (g : Var) : (nb078_alpha_dummy_455 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_455, fv_syn_c1c] using (nb078_compact_fv_empty_0347 g)

theorem nb078_compact_fv_empty_0348 : (nb078_alpha_dummy_454) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1144 : (nb078_alpha_dummy_454) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_454, fv_syn_c1c] using (nb078_compact_fv_empty_0348)

theorem nb078_compact_fv_empty_0349 (g : Var) : (nb078_alpha_dummy_456 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1145 (g : Var) : (nb078_alpha_dummy_456 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_456, fv_syn_c1c] using (nb078_compact_fv_empty_0349 g)

theorem nb078_compact_fv_empty_0350 : (nb078_alpha_dummy_446) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1146 : (nb078_alpha_dummy_446) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_446, fv_syn_c1c] using (nb078_compact_fv_empty_0350)

theorem nb078_compact_fv_empty_0351 (g : Var) : (nb078_alpha_dummy_448 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1147 (g : Var) : (nb078_alpha_dummy_448 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_448, fv_syn_c1c] using (nb078_compact_fv_empty_0351 g)

theorem nb078_compact_fv_empty_0352 : (nb078_alpha_dummy_445) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1148 : (nb078_alpha_dummy_445) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_445, fv_syn_c1c] using (nb078_compact_fv_empty_0352)

theorem nb078_compact_fv_empty_0353 (g : Var) : (nb078_alpha_dummy_447 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1149 (g : Var) : (nb078_alpha_dummy_447 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_447, fv_syn_c1c] using (nb078_compact_fv_empty_0353 g)

theorem nb078_compact_fv_empty_0354 : (nb078_alpha_dummy_451) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1150 : (nb078_alpha_dummy_451) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_451, fv_syn_c1c] using (nb078_compact_fv_empty_0354)

theorem nb078_compact_fv_empty_0355 (g : Var) : (nb078_alpha_dummy_452 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1151 (g : Var) : (nb078_alpha_dummy_452 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_452, fv_syn_c1c] using (nb078_compact_fv_empty_0355 g)

theorem nb078_compact_fv_empty_0356 : (nb078_alpha_dummy_449) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1152 : (nb078_alpha_dummy_449) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_449, fv_syn_c1c] using (nb078_compact_fv_empty_0356)

theorem nb078_compact_fv_empty_0357 (g : Var) : (nb078_alpha_dummy_450 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1153 (g : Var) : (nb078_alpha_dummy_450 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_450, fv_syn_c1c] using (nb078_compact_fv_empty_0357 g)

theorem nb078_compact_envfresh_0129 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460), (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)), ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_461) (nb078_alpha_dummy_464 g) (nb078_wpp_notmem_1134) (nb078_wpp_notmem_1135 g) (TEnvFresh.consFresh (nb078_alpha_dummy_460) (nb078_alpha_dummy_463 g) (nb078_wpp_notmem_1136) (nb078_wpp_notmem_1137 g) (TEnvFresh.consFresh (nb078_alpha_dummy_459) (nb078_alpha_dummy_462 g) (nb078_wpp_notmem_1138) (nb078_wpp_notmem_1139 g) (TEnvFresh.consFresh (nb078_alpha_dummy_457) (nb078_alpha_dummy_458 g) (nb078_wpp_notmem_1140) (nb078_wpp_notmem_1141 g) (TEnvFresh.consFresh (nb078_alpha_dummy_453) (nb078_alpha_dummy_455 g) (nb078_wpp_notmem_1142) (nb078_wpp_notmem_1143 g) (TEnvFresh.consFresh (nb078_alpha_dummy_454) (nb078_alpha_dummy_456 g) (nb078_wpp_notmem_1144) (nb078_wpp_notmem_1145 g) (TEnvFresh.consFresh (nb078_alpha_dummy_446) (nb078_alpha_dummy_448 g) (nb078_wpp_notmem_1146) (nb078_wpp_notmem_1147 g) (TEnvFresh.consFresh (nb078_alpha_dummy_445) (nb078_alpha_dummy_447 g) (nb078_wpp_notmem_1148) (nb078_wpp_notmem_1149 g) (TEnvFresh.consFresh (nb078_alpha_dummy_451) (nb078_alpha_dummy_452 g) (nb078_wpp_notmem_1150) (nb078_wpp_notmem_1151 g) (TEnvFresh.consFresh (nb078_alpha_dummy_449) (nb078_alpha_dummy_450 g) (nb078_wpp_notmem_1152) (nb078_wpp_notmem_1153 g) (TEnvFresh.consFresh (nb078_alpha_dummy_289) (nb078_alpha_dummy_292 g) (nb078_wpp_notmem_0876) (nb078_wpp_notmem_0877 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0746) (nb078_wpp_notmem_0747 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0748) (nb078_wpp_notmem_0749 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0750) (nb078_wpp_notmem_0751 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0752) (nb078_wpp_notmem_0753 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0754) (nb078_wpp_notmem_0755 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0129 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460), (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)), ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0129 x y g)

theorem nb078_wpp_notmem_1154 : (nb078_alpha_dummy_461) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_461, fv_syn_c0] using (nb078_compact_fv_empty_0338)

theorem nb078_wpp_notmem_1155 (g : Var) : (nb078_alpha_dummy_464 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_464, fv_syn_c0] using (nb078_compact_fv_empty_0339 g)

theorem nb078_wpp_notmem_1156 : (nb078_alpha_dummy_460) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_460, fv_syn_c0] using (nb078_compact_fv_empty_0340)

theorem nb078_wpp_notmem_1157 (g : Var) : (nb078_alpha_dummy_463 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_463, fv_syn_c0] using (nb078_compact_fv_empty_0341 g)

theorem nb078_wpp_notmem_1158 : (nb078_alpha_dummy_459) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_459, fv_syn_c0] using (nb078_compact_fv_empty_0342)

theorem nb078_wpp_notmem_1159 (g : Var) : (nb078_alpha_dummy_462 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_462, fv_syn_c0] using (nb078_compact_fv_empty_0343 g)

theorem nb078_wpp_notmem_1160 : (nb078_alpha_dummy_457) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_457, fv_syn_c0] using (nb078_compact_fv_empty_0344)

theorem nb078_wpp_notmem_1161 (g : Var) : (nb078_alpha_dummy_458 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_458, fv_syn_c0] using (nb078_compact_fv_empty_0345 g)

theorem nb078_wpp_notmem_1162 : (nb078_alpha_dummy_453) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_453, fv_syn_c0] using (nb078_compact_fv_empty_0346)

theorem nb078_wpp_notmem_1163 (g : Var) : (nb078_alpha_dummy_455 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_455, fv_syn_c0] using (nb078_compact_fv_empty_0347 g)

theorem nb078_wpp_notmem_1164 : (nb078_alpha_dummy_454) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_454, fv_syn_c0] using (nb078_compact_fv_empty_0348)

theorem nb078_wpp_notmem_1165 (g : Var) : (nb078_alpha_dummy_456 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_456, fv_syn_c0] using (nb078_compact_fv_empty_0349 g)

theorem nb078_wpp_notmem_1166 : (nb078_alpha_dummy_446) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_446, fv_syn_c0] using (nb078_compact_fv_empty_0350)

theorem nb078_wpp_notmem_1167 (g : Var) : (nb078_alpha_dummy_448 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_448, fv_syn_c0] using (nb078_compact_fv_empty_0351 g)

theorem nb078_wpp_notmem_1168 : (nb078_alpha_dummy_445) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_445, fv_syn_c0] using (nb078_compact_fv_empty_0352)

theorem nb078_wpp_notmem_1169 (g : Var) : (nb078_alpha_dummy_447 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_447, fv_syn_c0] using (nb078_compact_fv_empty_0353 g)

theorem nb078_wpp_notmem_1170 : (nb078_alpha_dummy_451) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_451, fv_syn_c0] using (nb078_compact_fv_empty_0354)

theorem nb078_wpp_notmem_1171 (g : Var) : (nb078_alpha_dummy_452 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_452, fv_syn_c0] using (nb078_compact_fv_empty_0355 g)

theorem nb078_wpp_notmem_1172 : (nb078_alpha_dummy_449) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_449, fv_syn_c0] using (nb078_compact_fv_empty_0356)

theorem nb078_wpp_notmem_1173 (g : Var) : (nb078_alpha_dummy_450 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_450, fv_syn_c0] using (nb078_compact_fv_empty_0357 g)

theorem nb078_compact_envfresh_0130 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460), (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)), ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_461) (nb078_alpha_dummy_464 g) (nb078_wpp_notmem_1154) (nb078_wpp_notmem_1155 g) (TEnvFresh.consFresh (nb078_alpha_dummy_460) (nb078_alpha_dummy_463 g) (nb078_wpp_notmem_1156) (nb078_wpp_notmem_1157 g) (TEnvFresh.consFresh (nb078_alpha_dummy_459) (nb078_alpha_dummy_462 g) (nb078_wpp_notmem_1158) (nb078_wpp_notmem_1159 g) (TEnvFresh.consFresh (nb078_alpha_dummy_457) (nb078_alpha_dummy_458 g) (nb078_wpp_notmem_1160) (nb078_wpp_notmem_1161 g) (TEnvFresh.consFresh (nb078_alpha_dummy_453) (nb078_alpha_dummy_455 g) (nb078_wpp_notmem_1162) (nb078_wpp_notmem_1163 g) (TEnvFresh.consFresh (nb078_alpha_dummy_454) (nb078_alpha_dummy_456 g) (nb078_wpp_notmem_1164) (nb078_wpp_notmem_1165 g) (TEnvFresh.consFresh (nb078_alpha_dummy_446) (nb078_alpha_dummy_448 g) (nb078_wpp_notmem_1166) (nb078_wpp_notmem_1167 g) (TEnvFresh.consFresh (nb078_alpha_dummy_445) (nb078_alpha_dummy_447 g) (nb078_wpp_notmem_1168) (nb078_wpp_notmem_1169 g) (TEnvFresh.consFresh (nb078_alpha_dummy_451) (nb078_alpha_dummy_452 g) (nb078_wpp_notmem_1170) (nb078_wpp_notmem_1171 g) (TEnvFresh.consFresh (nb078_alpha_dummy_449) (nb078_alpha_dummy_450 g) (nb078_wpp_notmem_1172) (nb078_wpp_notmem_1173 g) (TEnvFresh.consFresh (nb078_alpha_dummy_289) (nb078_alpha_dummy_292 g) (nb078_wpp_notmem_0898) (nb078_wpp_notmem_0899 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0778) (nb078_wpp_notmem_0779 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0780) (nb078_wpp_notmem_0781 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0782) (nb078_wpp_notmem_0783 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0784) (nb078_wpp_notmem_0785 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0786) (nb078_wpp_notmem_0787 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0788) (nb078_wpp_notmem_0789 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0130 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460), (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)), ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0130 x y g)

theorem nb078_wpp_notmem_1174 : (nb078_alpha_dummy_457) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_457, fv_syn_cnnc] using (nb078_compact_fv_empty_0344)

theorem nb078_wpp_notmem_1175 (g : Var) : (nb078_alpha_dummy_458 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_458, fv_syn_cnnc] using (nb078_compact_fv_empty_0345 g)

theorem nb078_wpp_notmem_1176 : (nb078_alpha_dummy_453) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_453, fv_syn_cnnc] using (nb078_compact_fv_empty_0346)

theorem nb078_wpp_notmem_1177 (g : Var) : (nb078_alpha_dummy_455 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_455, fv_syn_cnnc] using (nb078_compact_fv_empty_0347 g)

theorem nb078_wpp_notmem_1178 : (nb078_alpha_dummy_454) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_454, fv_syn_cnnc] using (nb078_compact_fv_empty_0348)

theorem nb078_wpp_notmem_1179 (g : Var) : (nb078_alpha_dummy_456 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_456, fv_syn_cnnc] using (nb078_compact_fv_empty_0349 g)

theorem nb078_wpp_notmem_1180 : (nb078_alpha_dummy_446) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_446, fv_syn_cnnc] using (nb078_compact_fv_empty_0350)

theorem nb078_wpp_notmem_1181 (g : Var) : (nb078_alpha_dummy_448 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_448, fv_syn_cnnc] using (nb078_compact_fv_empty_0351 g)

theorem nb078_wpp_notmem_1182 : (nb078_alpha_dummy_445) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_445, fv_syn_cnnc] using (nb078_compact_fv_empty_0352)

theorem nb078_wpp_notmem_1183 (g : Var) : (nb078_alpha_dummy_447 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_447, fv_syn_cnnc] using (nb078_compact_fv_empty_0353 g)

theorem nb078_wpp_notmem_1184 : (nb078_alpha_dummy_451) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_451, fv_syn_cnnc] using (nb078_compact_fv_empty_0354)

theorem nb078_wpp_notmem_1185 (g : Var) : (nb078_alpha_dummy_452 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_452, fv_syn_cnnc] using (nb078_compact_fv_empty_0355 g)

theorem nb078_wpp_notmem_1186 : (nb078_alpha_dummy_449) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_449, fv_syn_cnnc] using (nb078_compact_fv_empty_0356)

theorem nb078_wpp_notmem_1187 (g : Var) : (nb078_alpha_dummy_450 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_450, fv_syn_cnnc] using (nb078_compact_fv_empty_0357 g)

theorem nb078_compact_envfresh_0131 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_457) (nb078_alpha_dummy_458 g) (nb078_wpp_notmem_1174) (nb078_wpp_notmem_1175 g) (TEnvFresh.consFresh (nb078_alpha_dummy_453) (nb078_alpha_dummy_455 g) (nb078_wpp_notmem_1176) (nb078_wpp_notmem_1177 g) (TEnvFresh.consFresh (nb078_alpha_dummy_454) (nb078_alpha_dummy_456 g) (nb078_wpp_notmem_1178) (nb078_wpp_notmem_1179 g) (TEnvFresh.consFresh (nb078_alpha_dummy_446) (nb078_alpha_dummy_448 g) (nb078_wpp_notmem_1180) (nb078_wpp_notmem_1181 g) (TEnvFresh.consFresh (nb078_alpha_dummy_445) (nb078_alpha_dummy_447 g) (nb078_wpp_notmem_1182) (nb078_wpp_notmem_1183 g) (TEnvFresh.consFresh (nb078_alpha_dummy_451) (nb078_alpha_dummy_452 g) (nb078_wpp_notmem_1184) (nb078_wpp_notmem_1185 g) (TEnvFresh.consFresh (nb078_alpha_dummy_449) (nb078_alpha_dummy_450 g) (nb078_wpp_notmem_1186) (nb078_wpp_notmem_1187 g) (TEnvFresh.consFresh (nb078_alpha_dummy_289) (nb078_alpha_dummy_292 g) (nb078_wpp_notmem_0914) (nb078_wpp_notmem_0915 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0804) (nb078_wpp_notmem_0805 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0806) (nb078_wpp_notmem_0807 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0808) (nb078_wpp_notmem_0809 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0810) (nb078_wpp_notmem_0811 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0812) (nb078_wpp_notmem_0813 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0814) (nb078_wpp_notmem_0815 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb078_wpp_refl_0131 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0131 x y g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
