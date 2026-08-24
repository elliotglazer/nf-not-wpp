import NAR4C090C001Part062

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

noncomputable def nb090_wpp_refl_0145 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0145 v u A h)

noncomputable def nb090_split_alpha_0041 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_501 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_501 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))))) (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_502 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_502 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0480 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0481 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0480 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0481 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0510 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0511 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0508 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0509 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_468 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_470 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0484 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0485 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0484 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0485 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0482 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0483 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_483 A), (nb090_alpha_dummy_486 h)), ((nb090_alpha_dummy_482 A), (nb090_alpha_dummy_485 h)), ((nb090_alpha_dummy_481 A), (nb090_alpha_dummy_484 h)), ((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0143 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0488 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0489 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0486 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0487 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0492 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0493 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0490 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0491 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0488 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0489 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0486 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0487 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0492 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0493 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0490 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0491 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_483 A), (nb090_alpha_dummy_486 h)), ((nb090_alpha_dummy_482 A), (nb090_alpha_dummy_485 h)), ((nb090_alpha_dummy_481 A), (nb090_alpha_dummy_484 h)), ((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0144 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0496 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0497 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0494 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0495 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0496 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0497 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0494 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0495 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0500 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0501 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0498 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0499 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0500 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0501 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0498 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0499 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0482 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0483 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0145 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0482 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0483 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0482 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0483 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0145 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0480 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0481 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0480 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0481 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0510 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0511 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0508 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0509 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_468 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_470 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0484 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0485 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0484 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0485 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0482 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0483 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_483 A), (nb090_alpha_dummy_486 h)), ((nb090_alpha_dummy_482 A), (nb090_alpha_dummy_485 h)), ((nb090_alpha_dummy_481 A), (nb090_alpha_dummy_484 h)), ((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0143 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0488 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0489 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0486 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0487 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0492 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0493 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0490 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0491 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0488 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0489 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0486 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0487 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0492 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0493 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0490 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0491 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_483 A), (nb090_alpha_dummy_486 h)), ((nb090_alpha_dummy_482 A), (nb090_alpha_dummy_485 h)), ((nb090_alpha_dummy_481 A), (nb090_alpha_dummy_484 h)), ((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0144 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0496 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0497 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0494 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0495 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0496 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0497 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0494 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0495 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0500 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0501 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0498 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0499 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0500 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0501 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0498 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0499 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0482 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0483 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0145 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0482 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0483 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0482 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0483 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)), ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0145 v u A h))))))))))))))))))))

theorem nb090_wpp_notmem_1302 (A : Class) : (nb090_alpha_dummy_499 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_499, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0374 A)

theorem nb090_wpp_notmem_1303 (h : Var) : (nb090_alpha_dummy_500 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_500, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0375 h)

theorem nb090_wpp_notmem_1304 (A : Class) : (nb090_alpha_dummy_468 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_468, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0362 A)

theorem nb090_wpp_notmem_1305 (h : Var) : (nb090_alpha_dummy_470 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_470, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0363 h)

theorem nb090_wpp_notmem_1306 (A : Class) : (nb090_alpha_dummy_467 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_467, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0364 A)

theorem nb090_wpp_notmem_1307 (h : Var) : (nb090_alpha_dummy_469 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_469, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0365 h)

theorem nb090_wpp_notmem_1308 (A : Class) : (nb090_alpha_dummy_497 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_497, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0376 A)

theorem nb090_wpp_notmem_1309 (h : Var) : (nb090_alpha_dummy_498 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_498, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0377 h)

theorem nb090_wpp_notmem_1310 (A : Class) : (nb090_alpha_dummy_471 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_471, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0368 A)

theorem nb090_wpp_notmem_1311 (h : Var) : (nb090_alpha_dummy_472 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_472, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0369 h)

theorem nb090_wpp_notmem_1312 (A : Class) : (nb090_alpha_dummy_425 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_425, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0370 A)

theorem nb090_wpp_notmem_1313 (h : Var) : (nb090_alpha_dummy_428 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_428, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0371 h)

theorem nb090_compact_envfresh_0146 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_499 A) (nb090_alpha_dummy_500 h) (nb090_wpp_notmem_1302 A) (nb090_wpp_notmem_1303 h) (TEnvFresh.consFresh (nb090_alpha_dummy_468 A) (nb090_alpha_dummy_470 h) (nb090_wpp_notmem_1304 A) (nb090_wpp_notmem_1305 h) (TEnvFresh.consFresh (nb090_alpha_dummy_467 A) (nb090_alpha_dummy_469 h) (nb090_wpp_notmem_1306 A) (nb090_wpp_notmem_1307 h) (TEnvFresh.consFresh (nb090_alpha_dummy_497 A) (nb090_alpha_dummy_498 h) (nb090_wpp_notmem_1308 A) (nb090_wpp_notmem_1309 h) (TEnvFresh.consFresh (nb090_alpha_dummy_471 A) (nb090_alpha_dummy_472 h) (nb090_wpp_notmem_1310 A) (nb090_wpp_notmem_1311 h) (TEnvFresh.consFresh (nb090_alpha_dummy_425 A) (nb090_alpha_dummy_428 h) (nb090_wpp_notmem_1312 A) (nb090_wpp_notmem_1313 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1214 A) (nb090_wpp_notmem_1215 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1216 A) (nb090_wpp_notmem_1217 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1218 A) (nb090_wpp_notmem_1219 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1220 A) (nb090_wpp_notmem_1221 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1222 A) (nb090_wpp_notmem_1223 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))

noncomputable def nb090_wpp_refl_0146 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0146 v u A h)

theorem nb090_compact_fv_empty_0378 (A : Class) : (nb090_alpha_dummy_525 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1314 (A : Class) : (nb090_alpha_dummy_525 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_525, fv_syn_c1c] using (nb090_compact_fv_empty_0378 A)

theorem nb090_compact_fv_empty_0379 (h : Var) : (nb090_alpha_dummy_528 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1315 (h : Var) : (nb090_alpha_dummy_528 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_528, fv_syn_c1c] using (nb090_compact_fv_empty_0379 h)

theorem nb090_compact_fv_empty_0380 (A : Class) : (nb090_alpha_dummy_524 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1316 (A : Class) : (nb090_alpha_dummy_524 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_524, fv_syn_c1c] using (nb090_compact_fv_empty_0380 A)

theorem nb090_compact_fv_empty_0381 (h : Var) : (nb090_alpha_dummy_527 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1317 (h : Var) : (nb090_alpha_dummy_527 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_527, fv_syn_c1c] using (nb090_compact_fv_empty_0381 h)

theorem nb090_compact_fv_empty_0382 (A : Class) : (nb090_alpha_dummy_523 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1318 (A : Class) : (nb090_alpha_dummy_523 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_523, fv_syn_c1c] using (nb090_compact_fv_empty_0382 A)

theorem nb090_compact_fv_empty_0383 (h : Var) : (nb090_alpha_dummy_526 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1319 (h : Var) : (nb090_alpha_dummy_526 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_526, fv_syn_c1c] using (nb090_compact_fv_empty_0383 h)

theorem nb090_compact_fv_empty_0384 (A : Class) : (nb090_alpha_dummy_521 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1320 (A : Class) : (nb090_alpha_dummy_521 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_521, fv_syn_c1c] using (nb090_compact_fv_empty_0384 A)

theorem nb090_compact_fv_empty_0385 (h : Var) : (nb090_alpha_dummy_522 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1321 (h : Var) : (nb090_alpha_dummy_522 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_522, fv_syn_c1c] using (nb090_compact_fv_empty_0385 h)

theorem nb090_compact_fv_empty_0386 (A : Class) : (nb090_alpha_dummy_517 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1322 (A : Class) : (nb090_alpha_dummy_517 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_517, fv_syn_c1c] using (nb090_compact_fv_empty_0386 A)

theorem nb090_compact_fv_empty_0387 (h : Var) : (nb090_alpha_dummy_519 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1323 (h : Var) : (nb090_alpha_dummy_519 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_519, fv_syn_c1c] using (nb090_compact_fv_empty_0387 h)

theorem nb090_compact_fv_empty_0388 (A : Class) : (nb090_alpha_dummy_518 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1324 (A : Class) : (nb090_alpha_dummy_518 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_518, fv_syn_c1c] using (nb090_compact_fv_empty_0388 A)

theorem nb090_compact_fv_empty_0389 (h : Var) : (nb090_alpha_dummy_520 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1325 (h : Var) : (nb090_alpha_dummy_520 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_520, fv_syn_c1c] using (nb090_compact_fv_empty_0389 h)

theorem nb090_compact_fv_empty_0390 (A : Class) : (nb090_alpha_dummy_510 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1326 (A : Class) : (nb090_alpha_dummy_510 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_510, fv_syn_c1c] using (nb090_compact_fv_empty_0390 A)

theorem nb090_compact_fv_empty_0391 (h : Var) : (nb090_alpha_dummy_512 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1327 (h : Var) : (nb090_alpha_dummy_512 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_512, fv_syn_c1c] using (nb090_compact_fv_empty_0391 h)

theorem nb090_compact_fv_empty_0392 (A : Class) : (nb090_alpha_dummy_509 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1328 (A : Class) : (nb090_alpha_dummy_509 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_509, fv_syn_c1c] using (nb090_compact_fv_empty_0392 A)

theorem nb090_compact_fv_empty_0393 (h : Var) : (nb090_alpha_dummy_511 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1329 (h : Var) : (nb090_alpha_dummy_511 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_511, fv_syn_c1c] using (nb090_compact_fv_empty_0393 h)

theorem nb090_compact_fv_empty_0394 (A : Class) : (nb090_alpha_dummy_515 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1330 (A : Class) : (nb090_alpha_dummy_515 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_515, fv_syn_c1c] using (nb090_compact_fv_empty_0394 A)

theorem nb090_compact_fv_empty_0395 (h : Var) : (nb090_alpha_dummy_516 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1331 (h : Var) : (nb090_alpha_dummy_516 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_516, fv_syn_c1c] using (nb090_compact_fv_empty_0395 h)

theorem nb090_compact_fv_empty_0396 (A : Class) : (nb090_alpha_dummy_513 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1332 (A : Class) : (nb090_alpha_dummy_513 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_513, fv_syn_c1c] using (nb090_compact_fv_empty_0396 A)

theorem nb090_compact_fv_empty_0397 (h : Var) : (nb090_alpha_dummy_514 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1333 (h : Var) : (nb090_alpha_dummy_514 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_514, fv_syn_c1c] using (nb090_compact_fv_empty_0397 h)

theorem nb090_compact_fv_empty_0398 (A : Class) : (nb090_alpha_dummy_504 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1334 (A : Class) : (nb090_alpha_dummy_504 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_504, fv_syn_c1c] using (nb090_compact_fv_empty_0398 A)

theorem nb090_compact_fv_empty_0399 (h : Var) : (nb090_alpha_dummy_506 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1335 (h : Var) : (nb090_alpha_dummy_506 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_506, fv_syn_c1c] using (nb090_compact_fv_empty_0399 h)

theorem nb090_compact_fv_empty_0400 (A : Class) : (nb090_alpha_dummy_503 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1336 (A : Class) : (nb090_alpha_dummy_503 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_503, fv_syn_c1c] using (nb090_compact_fv_empty_0400 A)

theorem nb090_compact_fv_empty_0401 (h : Var) : (nb090_alpha_dummy_505 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1337 (h : Var) : (nb090_alpha_dummy_505 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_505, fv_syn_c1c] using (nb090_compact_fv_empty_0401 h)

theorem nb090_compact_fv_empty_0402 (A : Class) : (nb090_alpha_dummy_507 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1338 (A : Class) : (nb090_alpha_dummy_507 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_507, fv_syn_c1c] using (nb090_compact_fv_empty_0402 A)

theorem nb090_compact_fv_empty_0403 (h : Var) : (nb090_alpha_dummy_508 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1339 (h : Var) : (nb090_alpha_dummy_508 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_508, fv_syn_c1c] using (nb090_compact_fv_empty_0403 h)

theorem nb090_compact_envfresh_0147 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)), ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_525 A) (nb090_alpha_dummy_528 h) (nb090_wpp_notmem_1314 A) (nb090_wpp_notmem_1315 h) (TEnvFresh.consFresh (nb090_alpha_dummy_524 A) (nb090_alpha_dummy_527 h) (nb090_wpp_notmem_1316 A) (nb090_wpp_notmem_1317 h) (TEnvFresh.consFresh (nb090_alpha_dummy_523 A) (nb090_alpha_dummy_526 h) (nb090_wpp_notmem_1318 A) (nb090_wpp_notmem_1319 h) (TEnvFresh.consFresh (nb090_alpha_dummy_521 A) (nb090_alpha_dummy_522 h) (nb090_wpp_notmem_1320 A) (nb090_wpp_notmem_1321 h) (TEnvFresh.consFresh (nb090_alpha_dummy_517 A) (nb090_alpha_dummy_519 h) (nb090_wpp_notmem_1322 A) (nb090_wpp_notmem_1323 h) (TEnvFresh.consFresh (nb090_alpha_dummy_518 A) (nb090_alpha_dummy_520 h) (nb090_wpp_notmem_1324 A) (nb090_wpp_notmem_1325 h) (TEnvFresh.consFresh (nb090_alpha_dummy_510 A) (nb090_alpha_dummy_512 h) (nb090_wpp_notmem_1326 A) (nb090_wpp_notmem_1327 h) (TEnvFresh.consFresh (nb090_alpha_dummy_509 A) (nb090_alpha_dummy_511 h) (nb090_wpp_notmem_1328 A) (nb090_wpp_notmem_1329 h) (TEnvFresh.consFresh (nb090_alpha_dummy_515 A) (nb090_alpha_dummy_516 h) (nb090_wpp_notmem_1330 A) (nb090_wpp_notmem_1331 h) (TEnvFresh.consFresh (nb090_alpha_dummy_513 A) (nb090_alpha_dummy_514 h) (nb090_wpp_notmem_1332 A) (nb090_wpp_notmem_1333 h) (TEnvFresh.consFresh (nb090_alpha_dummy_504 A) (nb090_alpha_dummy_506 h) (nb090_wpp_notmem_1334 A) (nb090_wpp_notmem_1335 h) (TEnvFresh.consFresh (nb090_alpha_dummy_503 A) (nb090_alpha_dummy_505 h) (nb090_wpp_notmem_1336 A) (nb090_wpp_notmem_1337 h) (TEnvFresh.consFresh (nb090_alpha_dummy_507 A) (nb090_alpha_dummy_508 h) (nb090_wpp_notmem_1338 A) (nb090_wpp_notmem_1339 h) (TEnvFresh.consFresh (nb090_alpha_dummy_425 A) (nb090_alpha_dummy_428 h) (nb090_wpp_notmem_1244 A) (nb090_wpp_notmem_1245 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1122 A) (nb090_wpp_notmem_1123 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1124 A) (nb090_wpp_notmem_1125 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1126 A) (nb090_wpp_notmem_1127 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1128 A) (nb090_wpp_notmem_1129 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1130 A) (nb090_wpp_notmem_1131 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0147 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)), ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0147 v u A h)

theorem nb090_wpp_notmem_1340 (A : Class) : (nb090_alpha_dummy_525 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_525, fv_syn_c0] using (nb090_compact_fv_empty_0378 A)

theorem nb090_wpp_notmem_1341 (h : Var) : (nb090_alpha_dummy_528 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_528, fv_syn_c0] using (nb090_compact_fv_empty_0379 h)

theorem nb090_wpp_notmem_1342 (A : Class) : (nb090_alpha_dummy_524 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_524, fv_syn_c0] using (nb090_compact_fv_empty_0380 A)

theorem nb090_wpp_notmem_1343 (h : Var) : (nb090_alpha_dummy_527 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_527, fv_syn_c0] using (nb090_compact_fv_empty_0381 h)

theorem nb090_wpp_notmem_1344 (A : Class) : (nb090_alpha_dummy_523 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_523, fv_syn_c0] using (nb090_compact_fv_empty_0382 A)

theorem nb090_wpp_notmem_1345 (h : Var) : (nb090_alpha_dummy_526 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_526, fv_syn_c0] using (nb090_compact_fv_empty_0383 h)

theorem nb090_wpp_notmem_1346 (A : Class) : (nb090_alpha_dummy_521 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_521, fv_syn_c0] using (nb090_compact_fv_empty_0384 A)

theorem nb090_wpp_notmem_1347 (h : Var) : (nb090_alpha_dummy_522 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_522, fv_syn_c0] using (nb090_compact_fv_empty_0385 h)

theorem nb090_wpp_notmem_1348 (A : Class) : (nb090_alpha_dummy_517 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_517, fv_syn_c0] using (nb090_compact_fv_empty_0386 A)

theorem nb090_wpp_notmem_1349 (h : Var) : (nb090_alpha_dummy_519 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_519, fv_syn_c0] using (nb090_compact_fv_empty_0387 h)

theorem nb090_wpp_notmem_1350 (A : Class) : (nb090_alpha_dummy_518 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_518, fv_syn_c0] using (nb090_compact_fv_empty_0388 A)

theorem nb090_wpp_notmem_1351 (h : Var) : (nb090_alpha_dummy_520 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_520, fv_syn_c0] using (nb090_compact_fv_empty_0389 h)

theorem nb090_wpp_notmem_1352 (A : Class) : (nb090_alpha_dummy_510 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_510, fv_syn_c0] using (nb090_compact_fv_empty_0390 A)

theorem nb090_wpp_notmem_1353 (h : Var) : (nb090_alpha_dummy_512 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_512, fv_syn_c0] using (nb090_compact_fv_empty_0391 h)

theorem nb090_wpp_notmem_1354 (A : Class) : (nb090_alpha_dummy_509 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_509, fv_syn_c0] using (nb090_compact_fv_empty_0392 A)

theorem nb090_wpp_notmem_1355 (h : Var) : (nb090_alpha_dummy_511 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_511, fv_syn_c0] using (nb090_compact_fv_empty_0393 h)

theorem nb090_wpp_notmem_1356 (A : Class) : (nb090_alpha_dummy_515 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_515, fv_syn_c0] using (nb090_compact_fv_empty_0394 A)

theorem nb090_wpp_notmem_1357 (h : Var) : (nb090_alpha_dummy_516 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_516, fv_syn_c0] using (nb090_compact_fv_empty_0395 h)

theorem nb090_wpp_notmem_1358 (A : Class) : (nb090_alpha_dummy_513 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_513, fv_syn_c0] using (nb090_compact_fv_empty_0396 A)

theorem nb090_wpp_notmem_1359 (h : Var) : (nb090_alpha_dummy_514 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_514, fv_syn_c0] using (nb090_compact_fv_empty_0397 h)

theorem nb090_wpp_notmem_1360 (A : Class) : (nb090_alpha_dummy_504 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_504, fv_syn_c0] using (nb090_compact_fv_empty_0398 A)

theorem nb090_wpp_notmem_1361 (h : Var) : (nb090_alpha_dummy_506 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_506, fv_syn_c0] using (nb090_compact_fv_empty_0399 h)

theorem nb090_wpp_notmem_1362 (A : Class) : (nb090_alpha_dummy_503 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_503, fv_syn_c0] using (nb090_compact_fv_empty_0400 A)

theorem nb090_wpp_notmem_1363 (h : Var) : (nb090_alpha_dummy_505 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_505, fv_syn_c0] using (nb090_compact_fv_empty_0401 h)

theorem nb090_wpp_notmem_1364 (A : Class) : (nb090_alpha_dummy_507 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_507, fv_syn_c0] using (nb090_compact_fv_empty_0402 A)

theorem nb090_wpp_notmem_1365 (h : Var) : (nb090_alpha_dummy_508 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_508, fv_syn_c0] using (nb090_compact_fv_empty_0403 h)

theorem nb090_compact_envfresh_0148 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)), ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_525 A) (nb090_alpha_dummy_528 h) (nb090_wpp_notmem_1340 A) (nb090_wpp_notmem_1341 h) (TEnvFresh.consFresh (nb090_alpha_dummy_524 A) (nb090_alpha_dummy_527 h) (nb090_wpp_notmem_1342 A) (nb090_wpp_notmem_1343 h) (TEnvFresh.consFresh (nb090_alpha_dummy_523 A) (nb090_alpha_dummy_526 h) (nb090_wpp_notmem_1344 A) (nb090_wpp_notmem_1345 h) (TEnvFresh.consFresh (nb090_alpha_dummy_521 A) (nb090_alpha_dummy_522 h) (nb090_wpp_notmem_1346 A) (nb090_wpp_notmem_1347 h) (TEnvFresh.consFresh (nb090_alpha_dummy_517 A) (nb090_alpha_dummy_519 h) (nb090_wpp_notmem_1348 A) (nb090_wpp_notmem_1349 h) (TEnvFresh.consFresh (nb090_alpha_dummy_518 A) (nb090_alpha_dummy_520 h) (nb090_wpp_notmem_1350 A) (nb090_wpp_notmem_1351 h) (TEnvFresh.consFresh (nb090_alpha_dummy_510 A) (nb090_alpha_dummy_512 h) (nb090_wpp_notmem_1352 A) (nb090_wpp_notmem_1353 h) (TEnvFresh.consFresh (nb090_alpha_dummy_509 A) (nb090_alpha_dummy_511 h) (nb090_wpp_notmem_1354 A) (nb090_wpp_notmem_1355 h) (TEnvFresh.consFresh (nb090_alpha_dummy_515 A) (nb090_alpha_dummy_516 h) (nb090_wpp_notmem_1356 A) (nb090_wpp_notmem_1357 h) (TEnvFresh.consFresh (nb090_alpha_dummy_513 A) (nb090_alpha_dummy_514 h) (nb090_wpp_notmem_1358 A) (nb090_wpp_notmem_1359 h) (TEnvFresh.consFresh (nb090_alpha_dummy_504 A) (nb090_alpha_dummy_506 h) (nb090_wpp_notmem_1360 A) (nb090_wpp_notmem_1361 h) (TEnvFresh.consFresh (nb090_alpha_dummy_503 A) (nb090_alpha_dummy_505 h) (nb090_wpp_notmem_1362 A) (nb090_wpp_notmem_1363 h) (TEnvFresh.consFresh (nb090_alpha_dummy_507 A) (nb090_alpha_dummy_508 h) (nb090_wpp_notmem_1364 A) (nb090_wpp_notmem_1365 h) (TEnvFresh.consFresh (nb090_alpha_dummy_425 A) (nb090_alpha_dummy_428 h) (nb090_wpp_notmem_1266 A) (nb090_wpp_notmem_1267 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1152 A) (nb090_wpp_notmem_1153 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1154 A) (nb090_wpp_notmem_1155 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1156 A) (nb090_wpp_notmem_1157 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1158 A) (nb090_wpp_notmem_1159 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1160 A) (nb090_wpp_notmem_1161 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0148 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)), ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0148 v u A h)

theorem nb090_wpp_notmem_1366 (A : Class) : (nb090_alpha_dummy_521 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_521, fv_syn_cnnc] using (nb090_compact_fv_empty_0384 A)

theorem nb090_wpp_notmem_1367 (h : Var) : (nb090_alpha_dummy_522 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_522, fv_syn_cnnc] using (nb090_compact_fv_empty_0385 h)

theorem nb090_wpp_notmem_1368 (A : Class) : (nb090_alpha_dummy_517 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_517, fv_syn_cnnc] using (nb090_compact_fv_empty_0386 A)

theorem nb090_wpp_notmem_1369 (h : Var) : (nb090_alpha_dummy_519 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_519, fv_syn_cnnc] using (nb090_compact_fv_empty_0387 h)

theorem nb090_wpp_notmem_1370 (A : Class) : (nb090_alpha_dummy_518 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_518, fv_syn_cnnc] using (nb090_compact_fv_empty_0388 A)

theorem nb090_wpp_notmem_1371 (h : Var) : (nb090_alpha_dummy_520 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_520, fv_syn_cnnc] using (nb090_compact_fv_empty_0389 h)

theorem nb090_wpp_notmem_1372 (A : Class) : (nb090_alpha_dummy_510 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_510, fv_syn_cnnc] using (nb090_compact_fv_empty_0390 A)

theorem nb090_wpp_notmem_1373 (h : Var) : (nb090_alpha_dummy_512 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_512, fv_syn_cnnc] using (nb090_compact_fv_empty_0391 h)

theorem nb090_wpp_notmem_1374 (A : Class) : (nb090_alpha_dummy_509 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_509, fv_syn_cnnc] using (nb090_compact_fv_empty_0392 A)

theorem nb090_wpp_notmem_1375 (h : Var) : (nb090_alpha_dummy_511 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_511, fv_syn_cnnc] using (nb090_compact_fv_empty_0393 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
