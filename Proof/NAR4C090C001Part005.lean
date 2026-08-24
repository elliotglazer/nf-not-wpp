import NAR4C090C001Part004

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

noncomputable def nb090_alpha_dummy_600 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_601 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_602 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_603 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) 0)

noncomputable def nb090_alpha_dummy_604 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) 0)

noncomputable def nb090_alpha_dummy_605 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_596 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_597 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_606 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_599 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_600 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_607 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_596 A))).fv) 0)

noncomputable def nb090_alpha_dummy_608 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_599 h))).fv) 0)

noncomputable def nb090_alpha_dummy_609 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_597 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) 0)

noncomputable def nb090_alpha_dummy_610 (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_600 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) 0)

noncomputable def nb090_alpha_dummy_611 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_612 (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_613 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_614 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_615 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_616 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv) 0)

noncomputable def nb090_alpha_dummy_617 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) 0)

noncomputable def nb090_alpha_dummy_618 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) 1)

noncomputable def nb090_alpha_dummy_619 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_620 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) 1)

noncomputable def nb090_alpha_dummy_621 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_622 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_623 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_624 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_625 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_618 A))).fv) 0)

noncomputable def nb090_alpha_dummy_626 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_618 A))).fv) 1)

noncomputable def nb090_alpha_dummy_627 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_628 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) 1)

noncomputable def nb090_alpha_dummy_629 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_625 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_625 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_625 A))).fv) 0)

noncomputable def nb090_alpha_dummy_630 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_627 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_631 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_632 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_633 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_634 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_635 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_636 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_637 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_638 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h)) (Class.cv (nb090_alpha_dummy_636 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h)) (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_639 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) 0)

noncomputable def nb090_alpha_dummy_640 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_641 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_632 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_633 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_642 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_635 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_643 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_632 A))).fv) 0)

noncomputable def nb090_alpha_dummy_644 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_635 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_645 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_633 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) 0)

noncomputable def nb090_alpha_dummy_646 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_636 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_647 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_617 A) (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_648 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_649 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_650 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_651 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_652 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_653 (A : Class) : Var := (freshVar (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) 0)

noncomputable def nb090_alpha_dummy_654 (u : Var) : Var := (freshVar (((syn_c1st)).fv ∪ ((Class.cv u)).fv) 0)

noncomputable def nb090_alpha_dummy_655 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_653 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_653 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_656 (u : Var) : Var := (freshVar (({(nb090_alpha_dummy_654 u)} : Finset Var) ∪ ((syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))).fv) 0)

noncomputable def nb090_alpha_dummy_657 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_653 A) (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_653 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) 0)

noncomputable def nb090_alpha_dummy_658 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_653 A) (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_653 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) 1)

noncomputable def nb090_alpha_dummy_659 (u : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_654 u) (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))) (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) 0)

noncomputable def nb090_alpha_dummy_660 (u : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_654 u) (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))) (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) 1)

noncomputable def nb090_alpha_dummy_661 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) 0)

noncomputable def nb090_alpha_dummy_662 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) 1)

noncomputable def nb090_alpha_dummy_663 (u : Var) : Var := (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) 0)

noncomputable def nb090_alpha_dummy_664 (u : Var) : Var := (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) 1)

noncomputable def nb090_alpha_dummy_665 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_666 (u : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_667 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_668 (u : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv) 0)

noncomputable def nb090_alpha_dummy_669 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_662 A))).fv) 0)

noncomputable def nb090_alpha_dummy_670 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_662 A))).fv) 1)

noncomputable def nb090_alpha_dummy_671 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_664 u))).fv) 0)

noncomputable def nb090_alpha_dummy_672 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_664 u))).fv) 1)

noncomputable def nb090_alpha_dummy_673 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_669 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_669 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_669 A))).fv) 0)

noncomputable def nb090_alpha_dummy_674 (u : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_671 u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_671 u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_671 u))).fv) 0)

noncomputable def nb090_alpha_dummy_675 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_676 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_677 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_678 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_679 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_680 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_681 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_682 (u : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv) 0)

noncomputable def nb090_alpha_dummy_683 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) 0)

noncomputable def nb090_alpha_dummy_684 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) 0)

noncomputable def nb090_alpha_dummy_685 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_676 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_677 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_686 (u : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_679 u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_680 u)))).fv) 0)

noncomputable def nb090_alpha_dummy_687 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_676 A))).fv) 0)

noncomputable def nb090_alpha_dummy_688 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_679 u))).fv) 0)

noncomputable def nb090_alpha_dummy_689 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_677 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) 0)

noncomputable def nb090_alpha_dummy_690 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_680 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) 0)

noncomputable def nb090_alpha_dummy_691 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_661 A) (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_692 (u : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u)) (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_693 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_694 (u : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_695 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_696 (u : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv) 0)

noncomputable def nb090_alpha_dummy_697 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_655 A))).fv) 0)

noncomputable def nb090_alpha_dummy_698 (u : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_656 u))).fv) 0)

noncomputable def nb090_alpha_dummy_699 (A : Class) : Var := (freshVar (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_700 (A : Class) : Var := (freshVar (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) 1)

noncomputable def nb090_alpha_dummy_701 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_702 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) 1)

noncomputable def nb090_alpha_dummy_703 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_704 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_705 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_706 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_707 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_041 A))).fv) 0)

noncomputable def nb090_alpha_dummy_708 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_043 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_709 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_707 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_710 (v : Var) (u : Var) (h : Var) : Var := (freshVar (({(nb090_alpha_dummy_708 v u h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_711 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A) (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) 0)

noncomputable def nb090_alpha_dummy_712 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A) (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) 1)

noncomputable def nb090_alpha_dummy_713 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_708 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) 0)

noncomputable def nb090_alpha_dummy_714 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_708 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) 1)

noncomputable def nb090_alpha_dummy_715 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) 0)

noncomputable def nb090_alpha_dummy_716 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) 1)

noncomputable def nb090_alpha_dummy_717 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_718 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) 1)

noncomputable def nb090_alpha_dummy_719 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_720 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_721 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_722 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_723 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_716 A))).fv) 0)

noncomputable def nb090_alpha_dummy_724 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_716 A))).fv) 1)

noncomputable def nb090_alpha_dummy_725 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_726 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) 1)

noncomputable def nb090_alpha_dummy_727 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_723 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_723 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_723 A))).fv) 0)

noncomputable def nb090_alpha_dummy_728 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_725 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_729 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_730 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_731 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_732 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_733 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_734 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_735 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_736 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h)) (Class.cv (nb090_alpha_dummy_734 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h)) (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_737 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) 0)

noncomputable def nb090_alpha_dummy_738 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_739 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_730 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_731 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_740 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_733 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_741 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_730 A))).fv) 0)

noncomputable def nb090_alpha_dummy_742 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_733 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_743 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_731 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) 0)

noncomputable def nb090_alpha_dummy_744 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_734 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_745 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_746 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_747 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_748 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_749 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
