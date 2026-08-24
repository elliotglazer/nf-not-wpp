import NAR4C078C001Part078

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

noncomputable def nb078_split_alpha_0050 (x : Var) (y : Var) (g : Var) : TAlphaWff [((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_477)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446))))) (Wff.classMem (Class.cv (nb078_alpha_dummy_477)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_478 g)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))) (Wff.classMem (Class.cv (nb078_alpha_dummy_478 g)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0468) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0469 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0468) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0469 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0498) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0499 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0496) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0497 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_446))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_448 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0472) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0473 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0472) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0473 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0470) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0471 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460), (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)), ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0168 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0476) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0477 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0474) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0475 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0480) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0481 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0478) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0479 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0476) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0477 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0474) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0475 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0480) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0481 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0478) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0479 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460), (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)), ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0169 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0484) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0485 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0482) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0483 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0484) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0485 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0482) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0483 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0488) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0489 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0486) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0487 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0488) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0489 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0486) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0487 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0470) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0471 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0170 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0470) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0471 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0470) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0471 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0170 x y g)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0468) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0469 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0468) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0469 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0498) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0499 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0496) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0497 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_446))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_448 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0472) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0473 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0472) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0473 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0470) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0471 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460), (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)), ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0168 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0476) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0477 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0474) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0475 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0480) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0481 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0478) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0479 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0476) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0477 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0474) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0475 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0480) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0481 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0478) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0479 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460), (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)), ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0169 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0484) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0485 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0482) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0483 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0484) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0485 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0482) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0483 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0488) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0489 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0486) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0487 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0488) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0489 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0486) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0487 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0470) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0471 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0170 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0470) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0471 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0470) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0471 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)), ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0170 x y g)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (nb078_wpp_refl_0171 x y g)))))))

theorem nb078_compact_fv_empty_0364 : (nb078_alpha_dummy_482) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1222 : (nb078_alpha_dummy_482) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_482, fv_syn_cvv] using (nb078_compact_fv_empty_0364)

theorem nb078_compact_fv_empty_0365 (g : Var) : (nb078_alpha_dummy_484 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1223 (g : Var) : (nb078_alpha_dummy_484 g) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_484, fv_syn_cvv] using (nb078_compact_fv_empty_0365 g)

theorem nb078_compact_fv_empty_0366 : (nb078_alpha_dummy_481) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1224 : (nb078_alpha_dummy_481) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_481, fv_syn_cvv] using (nb078_compact_fv_empty_0366)

theorem nb078_compact_fv_empty_0367 (g : Var) : (nb078_alpha_dummy_483 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1225 (g : Var) : (nb078_alpha_dummy_483 g) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_483, fv_syn_cvv] using (nb078_compact_fv_empty_0367 g)

theorem nb078_wpp_notmem_1226 : (nb078_alpha_dummy_001) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_001, fv_syn_cvv] using (nb078_compact_fv_empty_0244)

theorem nb078_wpp_notmem_1227 (g : Var) : g ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb078_compact_fv_empty_0245 g)

theorem nb078_compact_envfresh_0172 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_482) (nb078_alpha_dummy_484 g) (nb078_wpp_notmem_1222) (nb078_wpp_notmem_1223 g) (TEnvFresh.consFresh (nb078_alpha_dummy_481) (nb078_alpha_dummy_483 g) (nb078_wpp_notmem_1224) (nb078_wpp_notmem_1225 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_1226) (nb078_wpp_notmem_1227 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0522) (nb078_wpp_notmem_0523 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0524) (nb078_wpp_notmem_0525 x) (TEnvFresh.nil ((syn_cvv)).fv))))))

noncomputable def nb078_wpp_refl_0172 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0172 x y g)

theorem nb078_compact_fv_empty_0368 : (nb078_alpha_dummy_501) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1228 : (nb078_alpha_dummy_501) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_501, fv_syn_c1c] using (nb078_compact_fv_empty_0368)

theorem nb078_compact_fv_empty_0369 (g : Var) : (nb078_alpha_dummy_504 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1229 (g : Var) : (nb078_alpha_dummy_504 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_504, fv_syn_c1c] using (nb078_compact_fv_empty_0369 g)

theorem nb078_compact_fv_empty_0370 : (nb078_alpha_dummy_500) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1230 : (nb078_alpha_dummy_500) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_500, fv_syn_c1c] using (nb078_compact_fv_empty_0370)

theorem nb078_compact_fv_empty_0371 (g : Var) : (nb078_alpha_dummy_503 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1231 (g : Var) : (nb078_alpha_dummy_503 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_503, fv_syn_c1c] using (nb078_compact_fv_empty_0371 g)

theorem nb078_compact_fv_empty_0372 : (nb078_alpha_dummy_499) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1232 : (nb078_alpha_dummy_499) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_499, fv_syn_c1c] using (nb078_compact_fv_empty_0372)

theorem nb078_compact_fv_empty_0373 (g : Var) : (nb078_alpha_dummy_502 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1233 (g : Var) : (nb078_alpha_dummy_502 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_502, fv_syn_c1c] using (nb078_compact_fv_empty_0373 g)

theorem nb078_compact_fv_empty_0374 : (nb078_alpha_dummy_497) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1234 : (nb078_alpha_dummy_497) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_497, fv_syn_c1c] using (nb078_compact_fv_empty_0374)

theorem nb078_compact_fv_empty_0375 (g : Var) : (nb078_alpha_dummy_498 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1235 (g : Var) : (nb078_alpha_dummy_498 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_498, fv_syn_c1c] using (nb078_compact_fv_empty_0375 g)

theorem nb078_compact_fv_empty_0376 : (nb078_alpha_dummy_493) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1236 : (nb078_alpha_dummy_493) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_493, fv_syn_c1c] using (nb078_compact_fv_empty_0376)

theorem nb078_compact_fv_empty_0377 (g : Var) : (nb078_alpha_dummy_495 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1237 (g : Var) : (nb078_alpha_dummy_495 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_495, fv_syn_c1c] using (nb078_compact_fv_empty_0377 g)

theorem nb078_compact_fv_empty_0378 : (nb078_alpha_dummy_494) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1238 : (nb078_alpha_dummy_494) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_494, fv_syn_c1c] using (nb078_compact_fv_empty_0378)

theorem nb078_compact_fv_empty_0379 (g : Var) : (nb078_alpha_dummy_496 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1239 (g : Var) : (nb078_alpha_dummy_496 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_496, fv_syn_c1c] using (nb078_compact_fv_empty_0379 g)

theorem nb078_compact_fv_empty_0380 : (nb078_alpha_dummy_486) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1240 : (nb078_alpha_dummy_486) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_486, fv_syn_c1c] using (nb078_compact_fv_empty_0380)

theorem nb078_compact_fv_empty_0381 (g : Var) : (nb078_alpha_dummy_488 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1241 (g : Var) : (nb078_alpha_dummy_488 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_488, fv_syn_c1c] using (nb078_compact_fv_empty_0381 g)

theorem nb078_compact_fv_empty_0382 : (nb078_alpha_dummy_485) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1242 : (nb078_alpha_dummy_485) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_485, fv_syn_c1c] using (nb078_compact_fv_empty_0382)

theorem nb078_compact_fv_empty_0383 (g : Var) : (nb078_alpha_dummy_487 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1243 (g : Var) : (nb078_alpha_dummy_487 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_487, fv_syn_c1c] using (nb078_compact_fv_empty_0383 g)

theorem nb078_compact_fv_empty_0384 : (nb078_alpha_dummy_491) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1244 : (nb078_alpha_dummy_491) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_491, fv_syn_c1c] using (nb078_compact_fv_empty_0384)

theorem nb078_compact_fv_empty_0385 (g : Var) : (nb078_alpha_dummy_492 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1245 (g : Var) : (nb078_alpha_dummy_492 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_492, fv_syn_c1c] using (nb078_compact_fv_empty_0385 g)

theorem nb078_compact_fv_empty_0386 : (nb078_alpha_dummy_489) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1246 : (nb078_alpha_dummy_489) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_489, fv_syn_c1c] using (nb078_compact_fv_empty_0386)

theorem nb078_compact_fv_empty_0387 (g : Var) : (nb078_alpha_dummy_490 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1247 (g : Var) : (nb078_alpha_dummy_490 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_490, fv_syn_c1c] using (nb078_compact_fv_empty_0387 g)

theorem nb078_wpp_notmem_1248 : (nb078_alpha_dummy_482) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_482, fv_syn_c1c] using (nb078_compact_fv_empty_0364)

theorem nb078_wpp_notmem_1249 (g : Var) : (nb078_alpha_dummy_484 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_484, fv_syn_c1c] using (nb078_compact_fv_empty_0365 g)

theorem nb078_wpp_notmem_1250 : (nb078_alpha_dummy_481) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_481, fv_syn_c1c] using (nb078_compact_fv_empty_0366)

theorem nb078_wpp_notmem_1251 (g : Var) : (nb078_alpha_dummy_483 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_483, fv_syn_c1c] using (nb078_compact_fv_empty_0367 g)

theorem nb078_compact_envfresh_0173 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500), (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)), ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_501) (nb078_alpha_dummy_504 g) (nb078_wpp_notmem_1228) (nb078_wpp_notmem_1229 g) (TEnvFresh.consFresh (nb078_alpha_dummy_500) (nb078_alpha_dummy_503 g) (nb078_wpp_notmem_1230) (nb078_wpp_notmem_1231 g) (TEnvFresh.consFresh (nb078_alpha_dummy_499) (nb078_alpha_dummy_502 g) (nb078_wpp_notmem_1232) (nb078_wpp_notmem_1233 g) (TEnvFresh.consFresh (nb078_alpha_dummy_497) (nb078_alpha_dummy_498 g) (nb078_wpp_notmem_1234) (nb078_wpp_notmem_1235 g) (TEnvFresh.consFresh (nb078_alpha_dummy_493) (nb078_alpha_dummy_495 g) (nb078_wpp_notmem_1236) (nb078_wpp_notmem_1237 g) (TEnvFresh.consFresh (nb078_alpha_dummy_494) (nb078_alpha_dummy_496 g) (nb078_wpp_notmem_1238) (nb078_wpp_notmem_1239 g) (TEnvFresh.consFresh (nb078_alpha_dummy_486) (nb078_alpha_dummy_488 g) (nb078_wpp_notmem_1240) (nb078_wpp_notmem_1241 g) (TEnvFresh.consFresh (nb078_alpha_dummy_485) (nb078_alpha_dummy_487 g) (nb078_wpp_notmem_1242) (nb078_wpp_notmem_1243 g) (TEnvFresh.consFresh (nb078_alpha_dummy_491) (nb078_alpha_dummy_492 g) (nb078_wpp_notmem_1244) (nb078_wpp_notmem_1245 g) (TEnvFresh.consFresh (nb078_alpha_dummy_489) (nb078_alpha_dummy_490 g) (nb078_wpp_notmem_1246) (nb078_wpp_notmem_1247 g) (TEnvFresh.consFresh (nb078_alpha_dummy_482) (nb078_alpha_dummy_484 g) (nb078_wpp_notmem_1248) (nb078_wpp_notmem_1249 g) (TEnvFresh.consFresh (nb078_alpha_dummy_481) (nb078_alpha_dummy_483 g) (nb078_wpp_notmem_1250) (nb078_wpp_notmem_1251 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0173 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500), (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)), ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0173 x y g)

theorem nb078_wpp_notmem_1252 : (nb078_alpha_dummy_501) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_501, fv_syn_c0] using (nb078_compact_fv_empty_0368)

theorem nb078_wpp_notmem_1253 (g : Var) : (nb078_alpha_dummy_504 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_504, fv_syn_c0] using (nb078_compact_fv_empty_0369 g)

theorem nb078_wpp_notmem_1254 : (nb078_alpha_dummy_500) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_500, fv_syn_c0] using (nb078_compact_fv_empty_0370)

theorem nb078_wpp_notmem_1255 (g : Var) : (nb078_alpha_dummy_503 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_503, fv_syn_c0] using (nb078_compact_fv_empty_0371 g)

theorem nb078_wpp_notmem_1256 : (nb078_alpha_dummy_499) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_499, fv_syn_c0] using (nb078_compact_fv_empty_0372)

theorem nb078_wpp_notmem_1257 (g : Var) : (nb078_alpha_dummy_502 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_502, fv_syn_c0] using (nb078_compact_fv_empty_0373 g)

theorem nb078_wpp_notmem_1258 : (nb078_alpha_dummy_497) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_497, fv_syn_c0] using (nb078_compact_fv_empty_0374)

theorem nb078_wpp_notmem_1259 (g : Var) : (nb078_alpha_dummy_498 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_498, fv_syn_c0] using (nb078_compact_fv_empty_0375 g)

theorem nb078_wpp_notmem_1260 : (nb078_alpha_dummy_493) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_493, fv_syn_c0] using (nb078_compact_fv_empty_0376)

theorem nb078_wpp_notmem_1261 (g : Var) : (nb078_alpha_dummy_495 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_495, fv_syn_c0] using (nb078_compact_fv_empty_0377 g)

theorem nb078_wpp_notmem_1262 : (nb078_alpha_dummy_494) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_494, fv_syn_c0] using (nb078_compact_fv_empty_0378)

theorem nb078_wpp_notmem_1263 (g : Var) : (nb078_alpha_dummy_496 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_496, fv_syn_c0] using (nb078_compact_fv_empty_0379 g)

theorem nb078_wpp_notmem_1264 : (nb078_alpha_dummy_486) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_486, fv_syn_c0] using (nb078_compact_fv_empty_0380)

theorem nb078_wpp_notmem_1265 (g : Var) : (nb078_alpha_dummy_488 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_488, fv_syn_c0] using (nb078_compact_fv_empty_0381 g)

theorem nb078_wpp_notmem_1266 : (nb078_alpha_dummy_485) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_485, fv_syn_c0] using (nb078_compact_fv_empty_0382)

theorem nb078_wpp_notmem_1267 (g : Var) : (nb078_alpha_dummy_487 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_487, fv_syn_c0] using (nb078_compact_fv_empty_0383 g)

theorem nb078_wpp_notmem_1268 : (nb078_alpha_dummy_491) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_491, fv_syn_c0] using (nb078_compact_fv_empty_0384)

theorem nb078_wpp_notmem_1269 (g : Var) : (nb078_alpha_dummy_492 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_492, fv_syn_c0] using (nb078_compact_fv_empty_0385 g)

theorem nb078_wpp_notmem_1270 : (nb078_alpha_dummy_489) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_489, fv_syn_c0] using (nb078_compact_fv_empty_0386)

theorem nb078_wpp_notmem_1271 (g : Var) : (nb078_alpha_dummy_490 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_490, fv_syn_c0] using (nb078_compact_fv_empty_0387 g)

theorem nb078_wpp_notmem_1272 : (nb078_alpha_dummy_482) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_482, fv_syn_c0] using (nb078_compact_fv_empty_0364)

theorem nb078_wpp_notmem_1273 (g : Var) : (nb078_alpha_dummy_484 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_484, fv_syn_c0] using (nb078_compact_fv_empty_0365 g)

theorem nb078_wpp_notmem_1274 : (nb078_alpha_dummy_481) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_481, fv_syn_c0] using (nb078_compact_fv_empty_0366)

theorem nb078_wpp_notmem_1275 (g : Var) : (nb078_alpha_dummy_483 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_483, fv_syn_c0] using (nb078_compact_fv_empty_0367 g)

theorem nb078_compact_envfresh_0174 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500), (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)), ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_501) (nb078_alpha_dummy_504 g) (nb078_wpp_notmem_1252) (nb078_wpp_notmem_1253 g) (TEnvFresh.consFresh (nb078_alpha_dummy_500) (nb078_alpha_dummy_503 g) (nb078_wpp_notmem_1254) (nb078_wpp_notmem_1255 g) (TEnvFresh.consFresh (nb078_alpha_dummy_499) (nb078_alpha_dummy_502 g) (nb078_wpp_notmem_1256) (nb078_wpp_notmem_1257 g) (TEnvFresh.consFresh (nb078_alpha_dummy_497) (nb078_alpha_dummy_498 g) (nb078_wpp_notmem_1258) (nb078_wpp_notmem_1259 g) (TEnvFresh.consFresh (nb078_alpha_dummy_493) (nb078_alpha_dummy_495 g) (nb078_wpp_notmem_1260) (nb078_wpp_notmem_1261 g) (TEnvFresh.consFresh (nb078_alpha_dummy_494) (nb078_alpha_dummy_496 g) (nb078_wpp_notmem_1262) (nb078_wpp_notmem_1263 g) (TEnvFresh.consFresh (nb078_alpha_dummy_486) (nb078_alpha_dummy_488 g) (nb078_wpp_notmem_1264) (nb078_wpp_notmem_1265 g) (TEnvFresh.consFresh (nb078_alpha_dummy_485) (nb078_alpha_dummy_487 g) (nb078_wpp_notmem_1266) (nb078_wpp_notmem_1267 g) (TEnvFresh.consFresh (nb078_alpha_dummy_491) (nb078_alpha_dummy_492 g) (nb078_wpp_notmem_1268) (nb078_wpp_notmem_1269 g) (TEnvFresh.consFresh (nb078_alpha_dummy_489) (nb078_alpha_dummy_490 g) (nb078_wpp_notmem_1270) (nb078_wpp_notmem_1271 g) (TEnvFresh.consFresh (nb078_alpha_dummy_482) (nb078_alpha_dummy_484 g) (nb078_wpp_notmem_1272) (nb078_wpp_notmem_1273 g) (TEnvFresh.consFresh (nb078_alpha_dummy_481) (nb078_alpha_dummy_483 g) (nb078_wpp_notmem_1274) (nb078_wpp_notmem_1275 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0788) (nb078_wpp_notmem_0789 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0174 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500), (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)), ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0174 x y g)

theorem nb078_wpp_notmem_1276 : (nb078_alpha_dummy_497) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_497, fv_syn_cnnc] using (nb078_compact_fv_empty_0374)

theorem nb078_wpp_notmem_1277 (g : Var) : (nb078_alpha_dummy_498 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_498, fv_syn_cnnc] using (nb078_compact_fv_empty_0375 g)

theorem nb078_wpp_notmem_1278 : (nb078_alpha_dummy_493) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_493, fv_syn_cnnc] using (nb078_compact_fv_empty_0376)

theorem nb078_wpp_notmem_1279 (g : Var) : (nb078_alpha_dummy_495 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_495, fv_syn_cnnc] using (nb078_compact_fv_empty_0377 g)

theorem nb078_wpp_notmem_1280 : (nb078_alpha_dummy_494) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_494, fv_syn_cnnc] using (nb078_compact_fv_empty_0378)

theorem nb078_wpp_notmem_1281 (g : Var) : (nb078_alpha_dummy_496 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_496, fv_syn_cnnc] using (nb078_compact_fv_empty_0379 g)

theorem nb078_wpp_notmem_1282 : (nb078_alpha_dummy_486) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_486, fv_syn_cnnc] using (nb078_compact_fv_empty_0380)

theorem nb078_wpp_notmem_1283 (g : Var) : (nb078_alpha_dummy_488 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_488, fv_syn_cnnc] using (nb078_compact_fv_empty_0381 g)

theorem nb078_wpp_notmem_1284 : (nb078_alpha_dummy_485) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_485, fv_syn_cnnc] using (nb078_compact_fv_empty_0382)

theorem nb078_wpp_notmem_1285 (g : Var) : (nb078_alpha_dummy_487 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_487, fv_syn_cnnc] using (nb078_compact_fv_empty_0383 g)

theorem nb078_wpp_notmem_1286 : (nb078_alpha_dummy_491) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_491, fv_syn_cnnc] using (nb078_compact_fv_empty_0384)

theorem nb078_wpp_notmem_1287 (g : Var) : (nb078_alpha_dummy_492 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_492, fv_syn_cnnc] using (nb078_compact_fv_empty_0385 g)

theorem nb078_wpp_notmem_1288 : (nb078_alpha_dummy_489) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_489, fv_syn_cnnc] using (nb078_compact_fv_empty_0386)

theorem nb078_wpp_notmem_1289 (g : Var) : (nb078_alpha_dummy_490 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_490, fv_syn_cnnc] using (nb078_compact_fv_empty_0387 g)

theorem nb078_wpp_notmem_1290 : (nb078_alpha_dummy_482) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_482, fv_syn_cnnc] using (nb078_compact_fv_empty_0364)

theorem nb078_wpp_notmem_1291 (g : Var) : (nb078_alpha_dummy_484 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_484, fv_syn_cnnc] using (nb078_compact_fv_empty_0365 g)

theorem nb078_wpp_notmem_1292 : (nb078_alpha_dummy_481) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_481, fv_syn_cnnc] using (nb078_compact_fv_empty_0366)

theorem nb078_wpp_notmem_1293 (g : Var) : (nb078_alpha_dummy_483 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_483, fv_syn_cnnc] using (nb078_compact_fv_empty_0367 g)

theorem nb078_compact_envfresh_0175 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_497) (nb078_alpha_dummy_498 g) (nb078_wpp_notmem_1276) (nb078_wpp_notmem_1277 g) (TEnvFresh.consFresh (nb078_alpha_dummy_493) (nb078_alpha_dummy_495 g) (nb078_wpp_notmem_1278) (nb078_wpp_notmem_1279 g) (TEnvFresh.consFresh (nb078_alpha_dummy_494) (nb078_alpha_dummy_496 g) (nb078_wpp_notmem_1280) (nb078_wpp_notmem_1281 g) (TEnvFresh.consFresh (nb078_alpha_dummy_486) (nb078_alpha_dummy_488 g) (nb078_wpp_notmem_1282) (nb078_wpp_notmem_1283 g) (TEnvFresh.consFresh (nb078_alpha_dummy_485) (nb078_alpha_dummy_487 g) (nb078_wpp_notmem_1284) (nb078_wpp_notmem_1285 g) (TEnvFresh.consFresh (nb078_alpha_dummy_491) (nb078_alpha_dummy_492 g) (nb078_wpp_notmem_1286) (nb078_wpp_notmem_1287 g) (TEnvFresh.consFresh (nb078_alpha_dummy_489) (nb078_alpha_dummy_490 g) (nb078_wpp_notmem_1288) (nb078_wpp_notmem_1289 g) (TEnvFresh.consFresh (nb078_alpha_dummy_482) (nb078_alpha_dummy_484 g) (nb078_wpp_notmem_1290) (nb078_wpp_notmem_1291 g) (TEnvFresh.consFresh (nb078_alpha_dummy_481) (nb078_alpha_dummy_483 g) (nb078_wpp_notmem_1292) (nb078_wpp_notmem_1293 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0814) (nb078_wpp_notmem_0815 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb078_wpp_refl_0175 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0175 x y g)

theorem nb078_compact_fv_empty_0388 : (nb078_alpha_dummy_519) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1294 : (nb078_alpha_dummy_519) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_519, fv_syn_c1c] using (nb078_compact_fv_empty_0388)

theorem nb078_compact_fv_empty_0389 (g : Var) : (nb078_alpha_dummy_520 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1295 (g : Var) : (nb078_alpha_dummy_520 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_520, fv_syn_c1c] using (nb078_compact_fv_empty_0389 g)

theorem nb078_compact_fv_empty_0390 : (nb078_alpha_dummy_517) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1296 : (nb078_alpha_dummy_517) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_517, fv_syn_c1c] using (nb078_compact_fv_empty_0390)

theorem nb078_compact_fv_empty_0391 (g : Var) : (nb078_alpha_dummy_518 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1297 (g : Var) : (nb078_alpha_dummy_518 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_518, fv_syn_c1c] using (nb078_compact_fv_empty_0391 g)

theorem nb078_compact_fv_empty_0392 : (nb078_alpha_dummy_515) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1298 : (nb078_alpha_dummy_515) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_515, fv_syn_c1c] using (nb078_compact_fv_empty_0392)

theorem nb078_compact_fv_empty_0393 (g : Var) : (nb078_alpha_dummy_516 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1299 (g : Var) : (nb078_alpha_dummy_516 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_516, fv_syn_c1c] using (nb078_compact_fv_empty_0393 g)

theorem nb078_compact_envfresh_0176 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500), (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)), ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_519), (nb078_alpha_dummy_520 g)), ((nb078_alpha_dummy_517), (nb078_alpha_dummy_518 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_515), (nb078_alpha_dummy_516 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_501) (nb078_alpha_dummy_504 g) (nb078_wpp_notmem_1228) (nb078_wpp_notmem_1229 g) (TEnvFresh.consFresh (nb078_alpha_dummy_500) (nb078_alpha_dummy_503 g) (nb078_wpp_notmem_1230) (nb078_wpp_notmem_1231 g) (TEnvFresh.consFresh (nb078_alpha_dummy_499) (nb078_alpha_dummy_502 g) (nb078_wpp_notmem_1232) (nb078_wpp_notmem_1233 g) (TEnvFresh.consFresh (nb078_alpha_dummy_497) (nb078_alpha_dummy_498 g) (nb078_wpp_notmem_1234) (nb078_wpp_notmem_1235 g) (TEnvFresh.consFresh (nb078_alpha_dummy_493) (nb078_alpha_dummy_495 g) (nb078_wpp_notmem_1236) (nb078_wpp_notmem_1237 g) (TEnvFresh.consFresh (nb078_alpha_dummy_494) (nb078_alpha_dummy_496 g) (nb078_wpp_notmem_1238) (nb078_wpp_notmem_1239 g) (TEnvFresh.consFresh (nb078_alpha_dummy_519) (nb078_alpha_dummy_520 g) (nb078_wpp_notmem_1294) (nb078_wpp_notmem_1295 g) (TEnvFresh.consFresh (nb078_alpha_dummy_517) (nb078_alpha_dummy_518 g) (nb078_wpp_notmem_1296) (nb078_wpp_notmem_1297 g) (TEnvFresh.consFresh (nb078_alpha_dummy_486) (nb078_alpha_dummy_488 g) (nb078_wpp_notmem_1240) (nb078_wpp_notmem_1241 g) (TEnvFresh.consFresh (nb078_alpha_dummy_485) (nb078_alpha_dummy_487 g) (nb078_wpp_notmem_1242) (nb078_wpp_notmem_1243 g) (TEnvFresh.consFresh (nb078_alpha_dummy_515) (nb078_alpha_dummy_516 g) (nb078_wpp_notmem_1298) (nb078_wpp_notmem_1299 g) (TEnvFresh.consFresh (nb078_alpha_dummy_489) (nb078_alpha_dummy_490 g) (nb078_wpp_notmem_1246) (nb078_wpp_notmem_1247 g) (TEnvFresh.consFresh (nb078_alpha_dummy_482) (nb078_alpha_dummy_484 g) (nb078_wpp_notmem_1248) (nb078_wpp_notmem_1249 g) (TEnvFresh.consFresh (nb078_alpha_dummy_481) (nb078_alpha_dummy_483 g) (nb078_wpp_notmem_1250) (nb078_wpp_notmem_1251 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0176 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500), (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)), ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_519), (nb078_alpha_dummy_520 g)), ((nb078_alpha_dummy_517), (nb078_alpha_dummy_518 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_515), (nb078_alpha_dummy_516 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0176 x y g)

theorem nb078_wpp_notmem_1300 : (nb078_alpha_dummy_519) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_519, fv_syn_c0] using (nb078_compact_fv_empty_0388)

theorem nb078_wpp_notmem_1301 (g : Var) : (nb078_alpha_dummy_520 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_520, fv_syn_c0] using (nb078_compact_fv_empty_0389 g)

theorem nb078_wpp_notmem_1302 : (nb078_alpha_dummy_517) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_517, fv_syn_c0] using (nb078_compact_fv_empty_0390)

theorem nb078_wpp_notmem_1303 (g : Var) : (nb078_alpha_dummy_518 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_518, fv_syn_c0] using (nb078_compact_fv_empty_0391 g)

theorem nb078_wpp_notmem_1304 : (nb078_alpha_dummy_515) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_515, fv_syn_c0] using (nb078_compact_fv_empty_0392)

theorem nb078_wpp_notmem_1305 (g : Var) : (nb078_alpha_dummy_516 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_516, fv_syn_c0] using (nb078_compact_fv_empty_0393 g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
