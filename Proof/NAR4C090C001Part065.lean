import NAR4C090C001Part064

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

noncomputable def nb090_split_alpha_0043 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_543 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_543 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))))) (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_544 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_544 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0522 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0523 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0522 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0523 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0552 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0553 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0550 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0551 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_510 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_512 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0526 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0527 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0526 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0527 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0524 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0525 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)), ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0150 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0530 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0531 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0528 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0529 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0534 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0535 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0532 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0533 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0530 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0531 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0528 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0529 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0534 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0535 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0532 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0533 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)), ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0151 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0538 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0539 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0536 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0537 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0538 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0539 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0536 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0537 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0542 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0543 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0540 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0541 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0542 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0543 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0540 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0541 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0524 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0525 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0152 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0524 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0525 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0524 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0525 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0152 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0522 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0523 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0522 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0523 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0552 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0553 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0550 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0551 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_510 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_512 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0526 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0527 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0526 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0527 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0524 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0525 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)), ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0150 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0530 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0531 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0528 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0529 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0534 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0535 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0532 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0533 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0530 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0531 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0528 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0529 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0534 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0535 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0532 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0533 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)), ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0151 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0538 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0539 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0536 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0537 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0538 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0539 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0536 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0537 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0542 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0543 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0540 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0541 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0542 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0543 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0540 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0541 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0524 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0525 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0152 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0524 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0525 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0524 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0525 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0152 v u A h))))))))))))))))))))

theorem nb090_wpp_notmem_1404 (A : Class) : (nb090_alpha_dummy_541 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_541, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0406 A)

theorem nb090_wpp_notmem_1405 (h : Var) : (nb090_alpha_dummy_542 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_542, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0407 h)

theorem nb090_wpp_notmem_1406 (A : Class) : (nb090_alpha_dummy_510 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_510, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0390 A)

theorem nb090_wpp_notmem_1407 (h : Var) : (nb090_alpha_dummy_512 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_512, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0391 h)

theorem nb090_wpp_notmem_1408 (A : Class) : (nb090_alpha_dummy_509 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_509, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0392 A)

theorem nb090_wpp_notmem_1409 (h : Var) : (nb090_alpha_dummy_511 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_511, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0393 h)

theorem nb090_wpp_notmem_1410 (A : Class) : (nb090_alpha_dummy_539 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_539, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0408 A)

theorem nb090_wpp_notmem_1411 (h : Var) : (nb090_alpha_dummy_540 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_540, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0409 h)

theorem nb090_wpp_notmem_1412 (A : Class) : (nb090_alpha_dummy_513 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_513, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0396 A)

theorem nb090_wpp_notmem_1413 (h : Var) : (nb090_alpha_dummy_514 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_514, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0397 h)

theorem nb090_wpp_notmem_1414 (A : Class) : (nb090_alpha_dummy_504 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_504, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0398 A)

theorem nb090_wpp_notmem_1415 (h : Var) : (nb090_alpha_dummy_506 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_506, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0399 h)

theorem nb090_wpp_notmem_1416 (A : Class) : (nb090_alpha_dummy_503 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_503, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0400 A)

theorem nb090_wpp_notmem_1417 (h : Var) : (nb090_alpha_dummy_505 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_505, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0401 h)

theorem nb090_wpp_notmem_1418 (A : Class) : (nb090_alpha_dummy_507 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_507, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0402 A)

theorem nb090_wpp_notmem_1419 (h : Var) : (nb090_alpha_dummy_508 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_508, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0403 h)

theorem nb090_compact_envfresh_0153 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_541 A) (nb090_alpha_dummy_542 h) (nb090_wpp_notmem_1404 A) (nb090_wpp_notmem_1405 h) (TEnvFresh.consFresh (nb090_alpha_dummy_510 A) (nb090_alpha_dummy_512 h) (nb090_wpp_notmem_1406 A) (nb090_wpp_notmem_1407 h) (TEnvFresh.consFresh (nb090_alpha_dummy_509 A) (nb090_alpha_dummy_511 h) (nb090_wpp_notmem_1408 A) (nb090_wpp_notmem_1409 h) (TEnvFresh.consFresh (nb090_alpha_dummy_539 A) (nb090_alpha_dummy_540 h) (nb090_wpp_notmem_1410 A) (nb090_wpp_notmem_1411 h) (TEnvFresh.consFresh (nb090_alpha_dummy_513 A) (nb090_alpha_dummy_514 h) (nb090_wpp_notmem_1412 A) (nb090_wpp_notmem_1413 h) (TEnvFresh.consFresh (nb090_alpha_dummy_504 A) (nb090_alpha_dummy_506 h) (nb090_wpp_notmem_1414 A) (nb090_wpp_notmem_1415 h) (TEnvFresh.consFresh (nb090_alpha_dummy_503 A) (nb090_alpha_dummy_505 h) (nb090_wpp_notmem_1416 A) (nb090_wpp_notmem_1417 h) (TEnvFresh.consFresh (nb090_alpha_dummy_507 A) (nb090_alpha_dummy_508 h) (nb090_wpp_notmem_1418 A) (nb090_wpp_notmem_1419 h) (TEnvFresh.consFresh (nb090_alpha_dummy_425 A) (nb090_alpha_dummy_428 h) (nb090_wpp_notmem_1312 A) (nb090_wpp_notmem_1313 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1214 A) (nb090_wpp_notmem_1215 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1216 A) (nb090_wpp_notmem_1217 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1218 A) (nb090_wpp_notmem_1219 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1220 A) (nb090_wpp_notmem_1221 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1222 A) (nb090_wpp_notmem_1223 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0153 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0153 v u A h)

theorem nb090_compact_fv_empty_0410 (A : Class) : (nb090_alpha_dummy_561 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1420 (A : Class) : (nb090_alpha_dummy_561 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_561, fv_syn_c1c] using (nb090_compact_fv_empty_0410 A)

theorem nb090_compact_fv_empty_0411 (h : Var) : (nb090_alpha_dummy_564 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1421 (h : Var) : (nb090_alpha_dummy_564 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_564, fv_syn_c1c] using (nb090_compact_fv_empty_0411 h)

theorem nb090_compact_fv_empty_0412 (A : Class) : (nb090_alpha_dummy_560 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1422 (A : Class) : (nb090_alpha_dummy_560 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_560, fv_syn_c1c] using (nb090_compact_fv_empty_0412 A)

theorem nb090_compact_fv_empty_0413 (h : Var) : (nb090_alpha_dummy_563 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1423 (h : Var) : (nb090_alpha_dummy_563 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_563, fv_syn_c1c] using (nb090_compact_fv_empty_0413 h)

theorem nb090_compact_fv_empty_0414 (A : Class) : (nb090_alpha_dummy_559 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1424 (A : Class) : (nb090_alpha_dummy_559 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_559, fv_syn_c1c] using (nb090_compact_fv_empty_0414 A)

theorem nb090_compact_fv_empty_0415 (h : Var) : (nb090_alpha_dummy_562 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1425 (h : Var) : (nb090_alpha_dummy_562 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_562, fv_syn_c1c] using (nb090_compact_fv_empty_0415 h)

theorem nb090_compact_fv_empty_0416 (A : Class) : (nb090_alpha_dummy_557 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1426 (A : Class) : (nb090_alpha_dummy_557 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_557, fv_syn_c1c] using (nb090_compact_fv_empty_0416 A)

theorem nb090_compact_fv_empty_0417 (h : Var) : (nb090_alpha_dummy_558 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1427 (h : Var) : (nb090_alpha_dummy_558 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_558, fv_syn_c1c] using (nb090_compact_fv_empty_0417 h)

theorem nb090_compact_fv_empty_0418 (A : Class) : (nb090_alpha_dummy_553 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1428 (A : Class) : (nb090_alpha_dummy_553 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_553, fv_syn_c1c] using (nb090_compact_fv_empty_0418 A)

theorem nb090_compact_fv_empty_0419 (h : Var) : (nb090_alpha_dummy_555 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1429 (h : Var) : (nb090_alpha_dummy_555 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_555, fv_syn_c1c] using (nb090_compact_fv_empty_0419 h)

theorem nb090_compact_fv_empty_0420 (A : Class) : (nb090_alpha_dummy_554 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1430 (A : Class) : (nb090_alpha_dummy_554 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_554, fv_syn_c1c] using (nb090_compact_fv_empty_0420 A)

theorem nb090_compact_fv_empty_0421 (h : Var) : (nb090_alpha_dummy_556 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1431 (h : Var) : (nb090_alpha_dummy_556 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_556, fv_syn_c1c] using (nb090_compact_fv_empty_0421 h)

theorem nb090_compact_fv_empty_0422 (A : Class) : (nb090_alpha_dummy_546 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1432 (A : Class) : (nb090_alpha_dummy_546 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_546, fv_syn_c1c] using (nb090_compact_fv_empty_0422 A)

theorem nb090_compact_fv_empty_0423 (h : Var) : (nb090_alpha_dummy_548 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1433 (h : Var) : (nb090_alpha_dummy_548 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_548, fv_syn_c1c] using (nb090_compact_fv_empty_0423 h)

theorem nb090_compact_fv_empty_0424 (A : Class) : (nb090_alpha_dummy_545 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1434 (A : Class) : (nb090_alpha_dummy_545 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_545, fv_syn_c1c] using (nb090_compact_fv_empty_0424 A)

theorem nb090_compact_fv_empty_0425 (h : Var) : (nb090_alpha_dummy_547 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1435 (h : Var) : (nb090_alpha_dummy_547 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_547, fv_syn_c1c] using (nb090_compact_fv_empty_0425 h)

theorem nb090_compact_fv_empty_0426 (A : Class) : (nb090_alpha_dummy_551 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1436 (A : Class) : (nb090_alpha_dummy_551 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_551, fv_syn_c1c] using (nb090_compact_fv_empty_0426 A)

theorem nb090_compact_fv_empty_0427 (h : Var) : (nb090_alpha_dummy_552 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1437 (h : Var) : (nb090_alpha_dummy_552 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_552, fv_syn_c1c] using (nb090_compact_fv_empty_0427 h)

theorem nb090_compact_fv_empty_0428 (A : Class) : (nb090_alpha_dummy_549 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1438 (A : Class) : (nb090_alpha_dummy_549 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_549, fv_syn_c1c] using (nb090_compact_fv_empty_0428 A)

theorem nb090_compact_fv_empty_0429 (h : Var) : (nb090_alpha_dummy_550 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1439 (h : Var) : (nb090_alpha_dummy_550 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_550, fv_syn_c1c] using (nb090_compact_fv_empty_0429 h)

theorem nb090_compact_envfresh_0154 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_561 A), (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A), (nb090_alpha_dummy_563 h)), ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)), ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)), ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)), ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)), ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)), ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_561 A) (nb090_alpha_dummy_564 h) (nb090_wpp_notmem_1420 A) (nb090_wpp_notmem_1421 h) (TEnvFresh.consFresh (nb090_alpha_dummy_560 A) (nb090_alpha_dummy_563 h) (nb090_wpp_notmem_1422 A) (nb090_wpp_notmem_1423 h) (TEnvFresh.consFresh (nb090_alpha_dummy_559 A) (nb090_alpha_dummy_562 h) (nb090_wpp_notmem_1424 A) (nb090_wpp_notmem_1425 h) (TEnvFresh.consFresh (nb090_alpha_dummy_557 A) (nb090_alpha_dummy_558 h) (nb090_wpp_notmem_1426 A) (nb090_wpp_notmem_1427 h) (TEnvFresh.consFresh (nb090_alpha_dummy_553 A) (nb090_alpha_dummy_555 h) (nb090_wpp_notmem_1428 A) (nb090_wpp_notmem_1429 h) (TEnvFresh.consFresh (nb090_alpha_dummy_554 A) (nb090_alpha_dummy_556 h) (nb090_wpp_notmem_1430 A) (nb090_wpp_notmem_1431 h) (TEnvFresh.consFresh (nb090_alpha_dummy_546 A) (nb090_alpha_dummy_548 h) (nb090_wpp_notmem_1432 A) (nb090_wpp_notmem_1433 h) (TEnvFresh.consFresh (nb090_alpha_dummy_545 A) (nb090_alpha_dummy_547 h) (nb090_wpp_notmem_1434 A) (nb090_wpp_notmem_1435 h) (TEnvFresh.consFresh (nb090_alpha_dummy_551 A) (nb090_alpha_dummy_552 h) (nb090_wpp_notmem_1436 A) (nb090_wpp_notmem_1437 h) (TEnvFresh.consFresh (nb090_alpha_dummy_549 A) (nb090_alpha_dummy_550 h) (nb090_wpp_notmem_1438 A) (nb090_wpp_notmem_1439 h) (TEnvFresh.consFresh (nb090_alpha_dummy_504 A) (nb090_alpha_dummy_506 h) (nb090_wpp_notmem_1334 A) (nb090_wpp_notmem_1335 h) (TEnvFresh.consFresh (nb090_alpha_dummy_503 A) (nb090_alpha_dummy_505 h) (nb090_wpp_notmem_1336 A) (nb090_wpp_notmem_1337 h) (TEnvFresh.consFresh (nb090_alpha_dummy_507 A) (nb090_alpha_dummy_508 h) (nb090_wpp_notmem_1338 A) (nb090_wpp_notmem_1339 h) (TEnvFresh.consFresh (nb090_alpha_dummy_425 A) (nb090_alpha_dummy_428 h) (nb090_wpp_notmem_1244 A) (nb090_wpp_notmem_1245 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1122 A) (nb090_wpp_notmem_1123 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1124 A) (nb090_wpp_notmem_1125 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1126 A) (nb090_wpp_notmem_1127 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1128 A) (nb090_wpp_notmem_1129 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1130 A) (nb090_wpp_notmem_1131 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0154 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_561 A), (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A), (nb090_alpha_dummy_563 h)), ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)), ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)), ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)), ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)), ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)), ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0154 v u A h)

theorem nb090_wpp_notmem_1440 (A : Class) : (nb090_alpha_dummy_561 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_561, fv_syn_c0] using (nb090_compact_fv_empty_0410 A)

theorem nb090_wpp_notmem_1441 (h : Var) : (nb090_alpha_dummy_564 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_564, fv_syn_c0] using (nb090_compact_fv_empty_0411 h)

theorem nb090_wpp_notmem_1442 (A : Class) : (nb090_alpha_dummy_560 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_560, fv_syn_c0] using (nb090_compact_fv_empty_0412 A)

theorem nb090_wpp_notmem_1443 (h : Var) : (nb090_alpha_dummy_563 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_563, fv_syn_c0] using (nb090_compact_fv_empty_0413 h)

theorem nb090_wpp_notmem_1444 (A : Class) : (nb090_alpha_dummy_559 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_559, fv_syn_c0] using (nb090_compact_fv_empty_0414 A)

theorem nb090_wpp_notmem_1445 (h : Var) : (nb090_alpha_dummy_562 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_562, fv_syn_c0] using (nb090_compact_fv_empty_0415 h)

theorem nb090_wpp_notmem_1446 (A : Class) : (nb090_alpha_dummy_557 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_557, fv_syn_c0] using (nb090_compact_fv_empty_0416 A)

theorem nb090_wpp_notmem_1447 (h : Var) : (nb090_alpha_dummy_558 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_558, fv_syn_c0] using (nb090_compact_fv_empty_0417 h)

theorem nb090_wpp_notmem_1448 (A : Class) : (nb090_alpha_dummy_553 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_553, fv_syn_c0] using (nb090_compact_fv_empty_0418 A)

theorem nb090_wpp_notmem_1449 (h : Var) : (nb090_alpha_dummy_555 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_555, fv_syn_c0] using (nb090_compact_fv_empty_0419 h)

theorem nb090_wpp_notmem_1450 (A : Class) : (nb090_alpha_dummy_554 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_554, fv_syn_c0] using (nb090_compact_fv_empty_0420 A)

theorem nb090_wpp_notmem_1451 (h : Var) : (nb090_alpha_dummy_556 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_556, fv_syn_c0] using (nb090_compact_fv_empty_0421 h)

theorem nb090_wpp_notmem_1452 (A : Class) : (nb090_alpha_dummy_546 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_546, fv_syn_c0] using (nb090_compact_fv_empty_0422 A)

theorem nb090_wpp_notmem_1453 (h : Var) : (nb090_alpha_dummy_548 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_548, fv_syn_c0] using (nb090_compact_fv_empty_0423 h)

theorem nb090_wpp_notmem_1454 (A : Class) : (nb090_alpha_dummy_545 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_545, fv_syn_c0] using (nb090_compact_fv_empty_0424 A)

theorem nb090_wpp_notmem_1455 (h : Var) : (nb090_alpha_dummy_547 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_547, fv_syn_c0] using (nb090_compact_fv_empty_0425 h)

theorem nb090_wpp_notmem_1456 (A : Class) : (nb090_alpha_dummy_551 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_551, fv_syn_c0] using (nb090_compact_fv_empty_0426 A)

theorem nb090_wpp_notmem_1457 (h : Var) : (nb090_alpha_dummy_552 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_552, fv_syn_c0] using (nb090_compact_fv_empty_0427 h)

theorem nb090_wpp_notmem_1458 (A : Class) : (nb090_alpha_dummy_549 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_549, fv_syn_c0] using (nb090_compact_fv_empty_0428 A)

theorem nb090_wpp_notmem_1459 (h : Var) : (nb090_alpha_dummy_550 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_550, fv_syn_c0] using (nb090_compact_fv_empty_0429 h)

theorem nb090_compact_envfresh_0155 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_561 A), (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A), (nb090_alpha_dummy_563 h)), ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)), ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)), ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)), ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)), ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)), ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_561 A) (nb090_alpha_dummy_564 h) (nb090_wpp_notmem_1440 A) (nb090_wpp_notmem_1441 h) (TEnvFresh.consFresh (nb090_alpha_dummy_560 A) (nb090_alpha_dummy_563 h) (nb090_wpp_notmem_1442 A) (nb090_wpp_notmem_1443 h) (TEnvFresh.consFresh (nb090_alpha_dummy_559 A) (nb090_alpha_dummy_562 h) (nb090_wpp_notmem_1444 A) (nb090_wpp_notmem_1445 h) (TEnvFresh.consFresh (nb090_alpha_dummy_557 A) (nb090_alpha_dummy_558 h) (nb090_wpp_notmem_1446 A) (nb090_wpp_notmem_1447 h) (TEnvFresh.consFresh (nb090_alpha_dummy_553 A) (nb090_alpha_dummy_555 h) (nb090_wpp_notmem_1448 A) (nb090_wpp_notmem_1449 h) (TEnvFresh.consFresh (nb090_alpha_dummy_554 A) (nb090_alpha_dummy_556 h) (nb090_wpp_notmem_1450 A) (nb090_wpp_notmem_1451 h) (TEnvFresh.consFresh (nb090_alpha_dummy_546 A) (nb090_alpha_dummy_548 h) (nb090_wpp_notmem_1452 A) (nb090_wpp_notmem_1453 h) (TEnvFresh.consFresh (nb090_alpha_dummy_545 A) (nb090_alpha_dummy_547 h) (nb090_wpp_notmem_1454 A) (nb090_wpp_notmem_1455 h) (TEnvFresh.consFresh (nb090_alpha_dummy_551 A) (nb090_alpha_dummy_552 h) (nb090_wpp_notmem_1456 A) (nb090_wpp_notmem_1457 h) (TEnvFresh.consFresh (nb090_alpha_dummy_549 A) (nb090_alpha_dummy_550 h) (nb090_wpp_notmem_1458 A) (nb090_wpp_notmem_1459 h) (TEnvFresh.consFresh (nb090_alpha_dummy_504 A) (nb090_alpha_dummy_506 h) (nb090_wpp_notmem_1360 A) (nb090_wpp_notmem_1361 h) (TEnvFresh.consFresh (nb090_alpha_dummy_503 A) (nb090_alpha_dummy_505 h) (nb090_wpp_notmem_1362 A) (nb090_wpp_notmem_1363 h) (TEnvFresh.consFresh (nb090_alpha_dummy_507 A) (nb090_alpha_dummy_508 h) (nb090_wpp_notmem_1364 A) (nb090_wpp_notmem_1365 h) (TEnvFresh.consFresh (nb090_alpha_dummy_425 A) (nb090_alpha_dummy_428 h) (nb090_wpp_notmem_1266 A) (nb090_wpp_notmem_1267 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1152 A) (nb090_wpp_notmem_1153 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1154 A) (nb090_wpp_notmem_1155 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1156 A) (nb090_wpp_notmem_1157 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1158 A) (nb090_wpp_notmem_1159 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1160 A) (nb090_wpp_notmem_1161 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0155 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_561 A), (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A), (nb090_alpha_dummy_563 h)), ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)), ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)), ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)), ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)), ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)), ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0155 v u A h)

theorem nb090_wpp_notmem_1460 (A : Class) : (nb090_alpha_dummy_557 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_557, fv_syn_cnnc] using (nb090_compact_fv_empty_0416 A)

theorem nb090_wpp_notmem_1461 (h : Var) : (nb090_alpha_dummy_558 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_558, fv_syn_cnnc] using (nb090_compact_fv_empty_0417 h)

theorem nb090_wpp_notmem_1462 (A : Class) : (nb090_alpha_dummy_553 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_553, fv_syn_cnnc] using (nb090_compact_fv_empty_0418 A)

theorem nb090_wpp_notmem_1463 (h : Var) : (nb090_alpha_dummy_555 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_555, fv_syn_cnnc] using (nb090_compact_fv_empty_0419 h)

theorem nb090_wpp_notmem_1464 (A : Class) : (nb090_alpha_dummy_554 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_554, fv_syn_cnnc] using (nb090_compact_fv_empty_0420 A)

theorem nb090_wpp_notmem_1465 (h : Var) : (nb090_alpha_dummy_556 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_556, fv_syn_cnnc] using (nb090_compact_fv_empty_0421 h)

theorem nb090_wpp_notmem_1466 (A : Class) : (nb090_alpha_dummy_546 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_546, fv_syn_cnnc] using (nb090_compact_fv_empty_0422 A)

theorem nb090_wpp_notmem_1467 (h : Var) : (nb090_alpha_dummy_548 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_548, fv_syn_cnnc] using (nb090_compact_fv_empty_0423 h)

theorem nb090_wpp_notmem_1468 (A : Class) : (nb090_alpha_dummy_545 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_545, fv_syn_cnnc] using (nb090_compact_fv_empty_0424 A)

theorem nb090_wpp_notmem_1469 (h : Var) : (nb090_alpha_dummy_547 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_547, fv_syn_cnnc] using (nb090_compact_fv_empty_0425 h)

theorem nb090_wpp_notmem_1470 (A : Class) : (nb090_alpha_dummy_551 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_551, fv_syn_cnnc] using (nb090_compact_fv_empty_0426 A)

theorem nb090_wpp_notmem_1471 (h : Var) : (nb090_alpha_dummy_552 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_552, fv_syn_cnnc] using (nb090_compact_fv_empty_0427 h)

theorem nb090_wpp_notmem_1472 (A : Class) : (nb090_alpha_dummy_549 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_549, fv_syn_cnnc] using (nb090_compact_fv_empty_0428 A)

theorem nb090_wpp_notmem_1473 (h : Var) : (nb090_alpha_dummy_550 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_550, fv_syn_cnnc] using (nb090_compact_fv_empty_0429 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
