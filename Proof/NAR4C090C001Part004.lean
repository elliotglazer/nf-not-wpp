import NAR4C090C001Part003

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

noncomputable def nb090_alpha_dummy_450 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_451 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_452 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_453 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) 0)

noncomputable def nb090_alpha_dummy_454 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) 0)

noncomputable def nb090_alpha_dummy_455 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_446 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_447 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_456 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_449 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_450 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_457 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_446 A))).fv) 0)

noncomputable def nb090_alpha_dummy_458 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_449 h))).fv) 0)

noncomputable def nb090_alpha_dummy_459 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_447 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) 0)

noncomputable def nb090_alpha_dummy_460 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_450 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) 0)

noncomputable def nb090_alpha_dummy_461 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_462 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_463 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_464 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_465 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_466 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_467 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) 0)

noncomputable def nb090_alpha_dummy_468 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) 1)

noncomputable def nb090_alpha_dummy_469 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) 0)

noncomputable def nb090_alpha_dummy_470 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) 1)

noncomputable def nb090_alpha_dummy_471 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_472 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_473 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_474 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_475 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_468 A))).fv) 0)

noncomputable def nb090_alpha_dummy_476 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_468 A))).fv) 1)

noncomputable def nb090_alpha_dummy_477 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_470 h))).fv) 0)

noncomputable def nb090_alpha_dummy_478 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_470 h))).fv) 1)

noncomputable def nb090_alpha_dummy_479 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_475 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_475 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_475 A))).fv) 0)

noncomputable def nb090_alpha_dummy_480 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_477 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_477 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_477 h))).fv) 0)

noncomputable def nb090_alpha_dummy_481 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_482 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_483 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_484 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_485 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_486 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_487 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_488 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_489 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) 0)

noncomputable def nb090_alpha_dummy_490 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) 0)

noncomputable def nb090_alpha_dummy_491 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_482 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_483 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_492 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_485 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_486 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_493 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_482 A))).fv) 0)

noncomputable def nb090_alpha_dummy_494 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_485 h))).fv) 0)

noncomputable def nb090_alpha_dummy_495 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_483 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) 0)

noncomputable def nb090_alpha_dummy_496 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_486 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) 0)

noncomputable def nb090_alpha_dummy_497 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_498 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_499 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_500 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_501 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_502 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_503 (A : Class) : Var := (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_504 (A : Class) : Var := (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 1)

noncomputable def nb090_alpha_dummy_505 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv) 0)

noncomputable def nb090_alpha_dummy_506 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv) 1)

noncomputable def nb090_alpha_dummy_507 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_503 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_508 (h : Var) : Var := (freshVar (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_505 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_509 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) 0)

noncomputable def nb090_alpha_dummy_510 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) 1)

noncomputable def nb090_alpha_dummy_511 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) 0)

noncomputable def nb090_alpha_dummy_512 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) 1)

noncomputable def nb090_alpha_dummy_513 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_514 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_515 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_516 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_517 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_510 A))).fv) 0)

noncomputable def nb090_alpha_dummy_518 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_510 A))).fv) 1)

noncomputable def nb090_alpha_dummy_519 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_512 h))).fv) 0)

noncomputable def nb090_alpha_dummy_520 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_512 h))).fv) 1)

noncomputable def nb090_alpha_dummy_521 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_517 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_517 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_517 A))).fv) 0)

noncomputable def nb090_alpha_dummy_522 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_519 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_519 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_519 h))).fv) 0)

noncomputable def nb090_alpha_dummy_523 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_524 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_525 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_526 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_527 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_528 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_529 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_530 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_531 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) 0)

noncomputable def nb090_alpha_dummy_532 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) 0)

noncomputable def nb090_alpha_dummy_533 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_524 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_525 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_534 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_527 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_528 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_535 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_524 A))).fv) 0)

noncomputable def nb090_alpha_dummy_536 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_527 h))).fv) 0)

noncomputable def nb090_alpha_dummy_537 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_525 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) 0)

noncomputable def nb090_alpha_dummy_538 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_528 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) 0)

noncomputable def nb090_alpha_dummy_539 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_540 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_541 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_542 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_543 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_544 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_545 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) 0)

noncomputable def nb090_alpha_dummy_546 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) 1)

noncomputable def nb090_alpha_dummy_547 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) 0)

noncomputable def nb090_alpha_dummy_548 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) 1)

noncomputable def nb090_alpha_dummy_549 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_550 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_551 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_552 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_553 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_546 A))).fv) 0)

noncomputable def nb090_alpha_dummy_554 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_546 A))).fv) 1)

noncomputable def nb090_alpha_dummy_555 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_548 h))).fv) 0)

noncomputable def nb090_alpha_dummy_556 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_548 h))).fv) 1)

noncomputable def nb090_alpha_dummy_557 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_553 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_553 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_553 A))).fv) 0)

noncomputable def nb090_alpha_dummy_558 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_555 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_555 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_555 h))).fv) 0)

noncomputable def nb090_alpha_dummy_559 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_560 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_561 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_562 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_563 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_564 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_565 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_566 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_567 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) 0)

noncomputable def nb090_alpha_dummy_568 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) 0)

noncomputable def nb090_alpha_dummy_569 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_560 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_561 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_570 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_563 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_564 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_571 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_560 A))).fv) 0)

noncomputable def nb090_alpha_dummy_572 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_563 h))).fv) 0)

noncomputable def nb090_alpha_dummy_573 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_561 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) 0)

noncomputable def nb090_alpha_dummy_574 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_564 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) 0)

noncomputable def nb090_alpha_dummy_575 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_576 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_577 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_578 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_579 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_580 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_581 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) 0)

noncomputable def nb090_alpha_dummy_582 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) 1)

noncomputable def nb090_alpha_dummy_583 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) 0)

noncomputable def nb090_alpha_dummy_584 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) 1)

noncomputable def nb090_alpha_dummy_585 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_586 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_587 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_588 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_589 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_582 A))).fv) 0)

noncomputable def nb090_alpha_dummy_590 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_582 A))).fv) 1)

noncomputable def nb090_alpha_dummy_591 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_584 h))).fv) 0)

noncomputable def nb090_alpha_dummy_592 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_584 h))).fv) 1)

noncomputable def nb090_alpha_dummy_593 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_589 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_589 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_589 A))).fv) 0)

noncomputable def nb090_alpha_dummy_594 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_591 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_591 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_591 h))).fv) 0)

noncomputable def nb090_alpha_dummy_595 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_596 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_597 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_598 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_599 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
