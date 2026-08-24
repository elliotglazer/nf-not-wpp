import NAR4C078C001Part003

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

noncomputable def nb078_alpha_dummy_450 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_451 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv) 0)

noncomputable def nb078_alpha_dummy_452 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_453 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_446))).fv) 0)

noncomputable def nb078_alpha_dummy_454 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_446))).fv) 1)

noncomputable def nb078_alpha_dummy_455 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_448 g))).fv) 0)

noncomputable def nb078_alpha_dummy_456 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_448 g))).fv) 1)

noncomputable def nb078_alpha_dummy_457 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_453)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_453)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_453))).fv) 0)

noncomputable def nb078_alpha_dummy_458 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_455 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_455 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_455 g))).fv) 0)

noncomputable def nb078_alpha_dummy_459 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_460 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_461 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_462 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_463 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_464 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_465 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv) 0)

noncomputable def nb078_alpha_dummy_466 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_467 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) 0)

noncomputable def nb078_alpha_dummy_468 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) 0)

noncomputable def nb078_alpha_dummy_469 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_460)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_461)))).fv) 0)

noncomputable def nb078_alpha_dummy_470 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_463 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_464 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_471 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_460))).fv) 0)

noncomputable def nb078_alpha_dummy_472 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_463 g))).fv) 0)

noncomputable def nb078_alpha_dummy_473 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_461))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) 0)

noncomputable def nb078_alpha_dummy_474 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_464 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) 0)

noncomputable def nb078_alpha_dummy_475 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_476 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_477 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_478 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_479 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv) 0)

noncomputable def nb078_alpha_dummy_480 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_481 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_482 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_483 (g : Var) : Var := (freshVar (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_484 (g : Var) : Var := (freshVar (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_485 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) 0)

noncomputable def nb078_alpha_dummy_486 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) 1)

noncomputable def nb078_alpha_dummy_487 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) 0)

noncomputable def nb078_alpha_dummy_488 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) 1)

noncomputable def nb078_alpha_dummy_489 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cphi (Class.cv (nb078_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_490 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_491 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv) 0)

noncomputable def nb078_alpha_dummy_492 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_493 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_486))).fv) 0)

noncomputable def nb078_alpha_dummy_494 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_486))).fv) 1)

noncomputable def nb078_alpha_dummy_495 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_488 g))).fv) 0)

noncomputable def nb078_alpha_dummy_496 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_488 g))).fv) 1)

noncomputable def nb078_alpha_dummy_497 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_493)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_493)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_493))).fv) 0)

noncomputable def nb078_alpha_dummy_498 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_495 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_495 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_495 g))).fv) 0)

noncomputable def nb078_alpha_dummy_499 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_500 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_501 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_502 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_503 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_504 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_505 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv) 0)

noncomputable def nb078_alpha_dummy_506 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_507 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) 0)

noncomputable def nb078_alpha_dummy_508 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) 0)

noncomputable def nb078_alpha_dummy_509 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_500)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_501)))).fv) 0)

noncomputable def nb078_alpha_dummy_510 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_503 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_504 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_511 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_500))).fv) 0)

noncomputable def nb078_alpha_dummy_512 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_503 g))).fv) 0)

noncomputable def nb078_alpha_dummy_513 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_501))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) 0)

noncomputable def nb078_alpha_dummy_514 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_504 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) 0)

noncomputable def nb078_alpha_dummy_515 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_516 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_517 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_486))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_518 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_519 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv) 0)

noncomputable def nb078_alpha_dummy_520 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_521 : Var := (freshVar (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_003)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_003)))).fv) 0)

noncomputable def nb078_alpha_dummy_522 (x : Var) (g : Var) : Var := (freshVar (((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv ∪ ((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv) 0)

noncomputable def nb078_alpha_dummy_523 : Var := (freshVar (((syn_crn (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((Class.cv (nb078_alpha_dummy_003))).fv) 0)

noncomputable def nb078_alpha_dummy_524 (x : Var) (g : Var) : Var := (freshVar (((syn_crn (Class.cv g))).fv ∪ ((Class.cv x)).fv) 0)

noncomputable def nb078_alpha_dummy_525 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_526 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_527 (g : Var) : Var := (freshVar (((Class.cv g)).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_528 (g : Var) : Var := (freshVar (((Class.cv g)).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_529 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) 0)

noncomputable def nb078_alpha_dummy_530 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) 1)

noncomputable def nb078_alpha_dummy_531 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) 0)

noncomputable def nb078_alpha_dummy_532 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) 1)

noncomputable def nb078_alpha_dummy_533 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_534 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_535 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv) 0)

noncomputable def nb078_alpha_dummy_536 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_537 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_530))).fv) 0)

noncomputable def nb078_alpha_dummy_538 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_530))).fv) 1)

noncomputable def nb078_alpha_dummy_539 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_532 g))).fv) 0)

noncomputable def nb078_alpha_dummy_540 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_532 g))).fv) 1)

noncomputable def nb078_alpha_dummy_541 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_537)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_537)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_537))).fv) 0)

noncomputable def nb078_alpha_dummy_542 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_539 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_539 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_539 g))).fv) 0)

noncomputable def nb078_alpha_dummy_543 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_544 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_545 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_546 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_547 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_548 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_549 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv) 0)

noncomputable def nb078_alpha_dummy_550 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_551 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) 0)

noncomputable def nb078_alpha_dummy_552 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) 0)

noncomputable def nb078_alpha_dummy_553 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_544)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_545)))).fv) 0)

noncomputable def nb078_alpha_dummy_554 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_547 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_548 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_555 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_544))).fv) 0)

noncomputable def nb078_alpha_dummy_556 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_547 g))).fv) 0)

noncomputable def nb078_alpha_dummy_557 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_545))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) 0)

noncomputable def nb078_alpha_dummy_558 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_548 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) 0)

noncomputable def nb078_alpha_dummy_559 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_560 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_561 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_530))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_562 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_563 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv) 0)

noncomputable def nb078_alpha_dummy_564 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_565 : Var := (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv) 0)

noncomputable def nb078_alpha_dummy_566 (g : Var) : Var := (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g)))) (syn_cid))).fv) 0)

noncomputable def nb078_alpha_dummy_567 : Var := (freshVar (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb078_alpha_dummy_568 (g : Var) : Var := (freshVar (((syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb078_alpha_dummy_569 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) 0)

noncomputable def nb078_alpha_dummy_570 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) 1)

noncomputable def nb078_alpha_dummy_571 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) 2)

noncomputable def nb078_alpha_dummy_572 (g : Var) : Var := (freshVar (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 0)

noncomputable def nb078_alpha_dummy_573 (g : Var) : Var := (freshVar (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 1)

noncomputable def nb078_alpha_dummy_574 (g : Var) : Var := (freshVar (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 2)

noncomputable def nb078_alpha_dummy_575 : Var := (freshVar (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_570)))))).fv) 0)

noncomputable def nb078_alpha_dummy_576 (g : Var) : Var := (freshVar (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_572 g)) (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_573 g)))))).fv) 0)

noncomputable def nb078_alpha_dummy_577 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 0)

noncomputable def nb078_alpha_dummy_578 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 1)

noncomputable def nb078_alpha_dummy_579 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) 0)

noncomputable def nb078_alpha_dummy_580 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) 1)

noncomputable def nb078_alpha_dummy_581 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cphi (Class.cv (nb078_alpha_dummy_578)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_582 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_583 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv) 0)

noncomputable def nb078_alpha_dummy_584 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_585 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_578))).fv) 0)

noncomputable def nb078_alpha_dummy_586 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_578))).fv) 1)

noncomputable def nb078_alpha_dummy_587 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_580 g))).fv) 0)

noncomputable def nb078_alpha_dummy_588 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_580 g))).fv) 1)

noncomputable def nb078_alpha_dummy_589 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_585)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_585)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_585))).fv) 0)

noncomputable def nb078_alpha_dummy_590 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_587 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_587 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_587 g))).fv) 0)

noncomputable def nb078_alpha_dummy_591 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_592 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_593 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_594 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_595 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_596 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_597 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv) 0)

noncomputable def nb078_alpha_dummy_598 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_599 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
