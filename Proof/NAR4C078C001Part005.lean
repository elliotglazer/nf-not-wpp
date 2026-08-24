import NAR4C078C001Part004

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

noncomputable def nb078_alpha_dummy_600 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) 0)

noncomputable def nb078_alpha_dummy_601 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_592)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_593)))).fv) 0)

noncomputable def nb078_alpha_dummy_602 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_595 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_596 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_603 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_592))).fv) 0)

noncomputable def nb078_alpha_dummy_604 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_595 g))).fv) 0)

noncomputable def nb078_alpha_dummy_605 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_593))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) 0)

noncomputable def nb078_alpha_dummy_606 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_596 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) 0)

noncomputable def nb078_alpha_dummy_607 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_608 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_609 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_578))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_610 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_611 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv) 0)

noncomputable def nb078_alpha_dummy_612 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_613 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) 0)

noncomputable def nb078_alpha_dummy_614 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) 1)

noncomputable def nb078_alpha_dummy_615 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) 0)

noncomputable def nb078_alpha_dummy_616 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) 1)

noncomputable def nb078_alpha_dummy_617 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cphi (Class.cv (nb078_alpha_dummy_614)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_618 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_619 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv) 0)

noncomputable def nb078_alpha_dummy_620 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_621 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_614))).fv) 0)

noncomputable def nb078_alpha_dummy_622 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_614))).fv) 1)

noncomputable def nb078_alpha_dummy_623 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_616 g))).fv) 0)

noncomputable def nb078_alpha_dummy_624 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_616 g))).fv) 1)

noncomputable def nb078_alpha_dummy_625 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_621)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_621)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_621))).fv) 0)

noncomputable def nb078_alpha_dummy_626 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_623 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_623 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_623 g))).fv) 0)

noncomputable def nb078_alpha_dummy_627 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_628 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_629 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_630 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_631 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_632 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_633 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv) 0)

noncomputable def nb078_alpha_dummy_634 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_635 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) 0)

noncomputable def nb078_alpha_dummy_636 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) 0)

noncomputable def nb078_alpha_dummy_637 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_628)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_629)))).fv) 0)

noncomputable def nb078_alpha_dummy_638 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_631 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_632 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_639 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_628))).fv) 0)

noncomputable def nb078_alpha_dummy_640 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_631 g))).fv) 0)

noncomputable def nb078_alpha_dummy_641 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_629))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) 0)

noncomputable def nb078_alpha_dummy_642 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_632 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) 0)

noncomputable def nb078_alpha_dummy_643 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_613) (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_613)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_644 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_615 g) (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_645 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_614))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_646 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_647 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv) 0)

noncomputable def nb078_alpha_dummy_648 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_649 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 0)

noncomputable def nb078_alpha_dummy_650 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 1)

noncomputable def nb078_alpha_dummy_651 (g : Var) : Var := (freshVar (((syn_ccnv (Class.cv g))).fv) 0)

noncomputable def nb078_alpha_dummy_652 (g : Var) : Var := (freshVar (((syn_ccnv (Class.cv g))).fv) 1)

noncomputable def nb078_alpha_dummy_653 : Var := (freshVar (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_650)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_649)))).fv) 0)

noncomputable def nb078_alpha_dummy_654 (g : Var) : Var := (freshVar (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_651 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_655 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) 0)

noncomputable def nb078_alpha_dummy_656 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) 1)

noncomputable def nb078_alpha_dummy_657 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) 0)

noncomputable def nb078_alpha_dummy_658 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) 1)

noncomputable def nb078_alpha_dummy_659 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cphi (Class.cv (nb078_alpha_dummy_656)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_660 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_661 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv) 0)

noncomputable def nb078_alpha_dummy_662 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_663 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_656))).fv) 0)

noncomputable def nb078_alpha_dummy_664 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_656))).fv) 1)

noncomputable def nb078_alpha_dummy_665 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_658 g))).fv) 0)

noncomputable def nb078_alpha_dummy_666 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_658 g))).fv) 1)

noncomputable def nb078_alpha_dummy_667 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_663)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_663)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_663))).fv) 0)

noncomputable def nb078_alpha_dummy_668 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_665 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_665 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_665 g))).fv) 0)

noncomputable def nb078_alpha_dummy_669 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_670 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_671 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_672 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_673 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_674 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_675 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv) 0)

noncomputable def nb078_alpha_dummy_676 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_677 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) 0)

noncomputable def nb078_alpha_dummy_678 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) 0)

noncomputable def nb078_alpha_dummy_679 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_670)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_671)))).fv) 0)

noncomputable def nb078_alpha_dummy_680 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_673 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_674 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_681 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_670))).fv) 0)

noncomputable def nb078_alpha_dummy_682 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_673 g))).fv) 0)

noncomputable def nb078_alpha_dummy_683 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_671))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) 0)

noncomputable def nb078_alpha_dummy_684 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_674 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) 0)

noncomputable def nb078_alpha_dummy_685 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_655) (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_655)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_686 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_657 g) (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_687 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_656))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_688 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_689 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv) 0)

noncomputable def nb078_alpha_dummy_690 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_691 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) 0)

noncomputable def nb078_alpha_dummy_692 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) 1)

noncomputable def nb078_alpha_dummy_693 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) 0)

noncomputable def nb078_alpha_dummy_694 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) 1)

noncomputable def nb078_alpha_dummy_695 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cphi (Class.cv (nb078_alpha_dummy_692)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_696 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_697 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv) 0)

noncomputable def nb078_alpha_dummy_698 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_699 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_692))).fv) 0)

noncomputable def nb078_alpha_dummy_700 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_692))).fv) 1)

noncomputable def nb078_alpha_dummy_701 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_694 g))).fv) 0)

noncomputable def nb078_alpha_dummy_702 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_694 g))).fv) 1)

noncomputable def nb078_alpha_dummy_703 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_699)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_699)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_699))).fv) 0)

noncomputable def nb078_alpha_dummy_704 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_701 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_701 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_701 g))).fv) 0)

noncomputable def nb078_alpha_dummy_705 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_706 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_707 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_708 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_709 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_710 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_711 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv) 0)

noncomputable def nb078_alpha_dummy_712 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_713 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) 0)

noncomputable def nb078_alpha_dummy_714 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) 0)

noncomputable def nb078_alpha_dummy_715 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_706)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_707)))).fv) 0)

noncomputable def nb078_alpha_dummy_716 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_709 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_710 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_717 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_706))).fv) 0)

noncomputable def nb078_alpha_dummy_718 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_709 g))).fv) 0)

noncomputable def nb078_alpha_dummy_719 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_707))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) 0)

noncomputable def nb078_alpha_dummy_720 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_710 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) 0)

noncomputable def nb078_alpha_dummy_721 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_691) (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649)) (Wff.classEq (Class.cv (nb078_alpha_dummy_691)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_722 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_693 g) (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_723 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_692))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_724 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_725 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv) 0)

noncomputable def nb078_alpha_dummy_726 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_727 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 0)

noncomputable def nb078_alpha_dummy_728 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) 1)

noncomputable def nb078_alpha_dummy_729 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) 0)

noncomputable def nb078_alpha_dummy_730 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) 1)

noncomputable def nb078_alpha_dummy_731 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cphi (Class.cv (nb078_alpha_dummy_728)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_732 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_733 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv) 0)

noncomputable def nb078_alpha_dummy_734 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv) 0)

noncomputable def nb078_alpha_dummy_735 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_728))).fv) 0)

noncomputable def nb078_alpha_dummy_736 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_728))).fv) 1)

noncomputable def nb078_alpha_dummy_737 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_730 g))).fv) 0)

noncomputable def nb078_alpha_dummy_738 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_730 g))).fv) 1)

noncomputable def nb078_alpha_dummy_739 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_735)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_735)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_735))).fv) 0)

noncomputable def nb078_alpha_dummy_740 (g : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_737 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_737 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_737 g))).fv) 0)

noncomputable def nb078_alpha_dummy_741 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_742 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_743 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_744 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_745 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_746 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_747 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv) 0)

noncomputable def nb078_alpha_dummy_748 (g : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_749 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
