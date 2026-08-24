import NAR4C090C001Part108

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

noncomputable def nb090_split_alpha_0087 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_695 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_695 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))))) (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_696 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_696 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0694 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0695 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0694 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0695 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0724 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0725 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0722 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0723 u) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_662 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_664 u))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0698 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0699 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0698 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0699 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0696 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0697 u) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)), ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0294 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0702 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0703 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0700 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0701 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0706 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0707 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0704 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0705 u) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0702 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0703 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0700 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0701 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0706 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0707 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0704 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0705 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)), ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0295 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0710 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0711 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0708 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0709 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0710 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0711 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0708 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0709 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0714 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0715 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0712 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0713 u) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0714 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0715 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0712 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0713 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0696 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0697 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0296 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0696 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0697 u) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0696 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0697 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0296 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0694 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0695 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0694 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0695 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0724 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0725 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0722 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0723 u) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_662 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_664 u))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0698 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0699 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0698 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0699 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0696 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0697 u) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)), ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0294 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0702 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0703 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0700 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0701 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0706 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0707 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0704 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0705 u) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0702 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0703 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0700 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0701 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0706 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0707 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0704 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0705 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)), ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0295 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0710 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0711 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0708 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0709 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0710 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0711 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0708 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0709 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0714 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0715 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0712 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0713 u) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0714 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0715 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0712 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0713 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0696 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0697 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0296 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0696 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0697 u) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0696 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0697 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0296 v u A h))))))))))))))))))))

theorem nb090_wpp_notmem_1786 (A : Class) : (nb090_alpha_dummy_693 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_693, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0522 A)

theorem nb090_wpp_notmem_1787 (u : Var) : (nb090_alpha_dummy_694 u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_694, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0523 u)

theorem nb090_wpp_notmem_1788 (A : Class) : (nb090_alpha_dummy_662 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_662, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0504 A)

theorem nb090_wpp_notmem_1789 (u : Var) : (nb090_alpha_dummy_664 u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_664, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0505 u)

theorem nb090_wpp_notmem_1790 (A : Class) : (nb090_alpha_dummy_661 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_661, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0506 A)

theorem nb090_wpp_notmem_1791 (u : Var) : (nb090_alpha_dummy_663 u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_663, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0507 u)

theorem nb090_wpp_notmem_1792 (A : Class) : (nb090_alpha_dummy_691 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_691, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0524 A)

theorem nb090_wpp_notmem_1793 (u : Var) : (nb090_alpha_dummy_692 u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_692, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0525 u)

theorem nb090_wpp_notmem_1794 (A : Class) : (nb090_alpha_dummy_665 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_665, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0510 A)

theorem nb090_wpp_notmem_1795 (u : Var) : (nb090_alpha_dummy_666 u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_666, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0511 u)

theorem nb090_wpp_notmem_1796 (A : Class) : (nb090_alpha_dummy_653 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_653, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0512 A)

theorem nb090_wpp_notmem_1797 (u : Var) : (nb090_alpha_dummy_654 u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_654, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0513 u)

theorem nb090_wpp_notmem_1798 (A : Class) : (nb090_alpha_dummy_655 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_655, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0514 A)

theorem nb090_wpp_notmem_1799 (u : Var) : (nb090_alpha_dummy_656 u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_656, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0515 u)

theorem nb090_wpp_notmem_1800 (A : Class) : (nb090_alpha_dummy_658 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_658, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0516 A)

theorem nb090_wpp_notmem_1801 (u : Var) : (nb090_alpha_dummy_660 u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_660, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0517 u)

theorem nb090_wpp_notmem_1802 (A : Class) : (nb090_alpha_dummy_657 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_657, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0518 A)

theorem nb090_wpp_notmem_1803 (u : Var) : (nb090_alpha_dummy_659 u) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_659, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0519 u)

theorem nb090_compact_envfresh_0297 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_693 A) (nb090_alpha_dummy_694 u) (nb090_wpp_notmem_1786 A) (nb090_wpp_notmem_1787 u) (TEnvFresh.consFresh (nb090_alpha_dummy_662 A) (nb090_alpha_dummy_664 u) (nb090_wpp_notmem_1788 A) (nb090_wpp_notmem_1789 u) (TEnvFresh.consFresh (nb090_alpha_dummy_661 A) (nb090_alpha_dummy_663 u) (nb090_wpp_notmem_1790 A) (nb090_wpp_notmem_1791 u) (TEnvFresh.consFresh (nb090_alpha_dummy_691 A) (nb090_alpha_dummy_692 u) (nb090_wpp_notmem_1792 A) (nb090_wpp_notmem_1793 u) (TEnvFresh.consFresh (nb090_alpha_dummy_665 A) (nb090_alpha_dummy_666 u) (nb090_wpp_notmem_1794 A) (nb090_wpp_notmem_1795 u) (TEnvFresh.consFresh (nb090_alpha_dummy_653 A) (nb090_alpha_dummy_654 u) (nb090_wpp_notmem_1796 A) (nb090_wpp_notmem_1797 u) (TEnvFresh.consFresh (nb090_alpha_dummy_655 A) (nb090_alpha_dummy_656 u) (nb090_wpp_notmem_1798 A) (nb090_wpp_notmem_1799 u) (TEnvFresh.consFresh (nb090_alpha_dummy_658 A) (nb090_alpha_dummy_660 u) (nb090_wpp_notmem_1800 A) (nb090_wpp_notmem_1801 u) (TEnvFresh.consFresh (nb090_alpha_dummy_657 A) (nb090_alpha_dummy_659 u) (nb090_wpp_notmem_1802 A) (nb090_wpp_notmem_1803 u) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1604 A) (nb090_wpp_notmem_1605 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1594 A) (nb090_wpp_notmem_1595 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))

noncomputable def nb090_wpp_refl_0297 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0297 v u A h)

theorem nb090_wpp_notmem_1804 (A : Class) : (nb090_alpha_dummy_653 A) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_653, fv_syn_c1st] using (nb090_compact_fv_empty_0512 A)

theorem nb090_wpp_notmem_1805 (u : Var) : (nb090_alpha_dummy_654 u) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_654, fv_syn_c1st] using (nb090_compact_fv_empty_0513 u)

theorem nb090_wpp_notmem_1806 (A : Class) : (nb090_alpha_dummy_655 A) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_655, fv_syn_c1st] using (nb090_compact_fv_empty_0514 A)

theorem nb090_wpp_notmem_1807 (u : Var) : (nb090_alpha_dummy_656 u) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_656, fv_syn_c1st] using (nb090_compact_fv_empty_0515 u)

theorem nb090_wpp_notmem_1808 (A : Class) : (nb090_alpha_dummy_658 A) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_658, fv_syn_c1st] using (nb090_compact_fv_empty_0516 A)

theorem nb090_wpp_notmem_1809 (u : Var) : (nb090_alpha_dummy_660 u) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_660, fv_syn_c1st] using (nb090_compact_fv_empty_0517 u)

theorem nb090_wpp_notmem_1810 (A : Class) : (nb090_alpha_dummy_657 A) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_657, fv_syn_c1st] using (nb090_compact_fv_empty_0518 A)

theorem nb090_wpp_notmem_1811 (u : Var) : (nb090_alpha_dummy_659 u) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_659, fv_syn_c1st] using (nb090_compact_fv_empty_0519 u)

theorem nb090_wpp_notmem_1812 (A : Class) : (nb090_alpha_dummy_042 A) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_042, fv_syn_c1st] using (nb090_compact_fv_empty_0464 A)

theorem nb090_wpp_notmem_1813 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_044, fv_syn_c1st] using (nb090_compact_fv_empty_0465 v u h)

theorem nb090_wpp_notmem_1814 (A : Class) : (nb090_alpha_dummy_041 A) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_041, fv_syn_c1st] using (nb090_compact_fv_empty_0462 A)

theorem nb090_wpp_notmem_1815 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_043 v u h) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_043, fv_syn_c1st] using (nb090_compact_fv_empty_0463 v u h)

theorem nb090_wpp_notmem_1816 (A : Class) : (nb090_alpha_dummy_000 A) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_000, fv_syn_c1st] using (nb090_compact_fv_empty_0062 A)

theorem nb090_wpp_notmem_1817 (h : Var) : h ∉ ((syn_c1st)).fv := by
  simpa only [fv_syn_c1st] using (nb090_compact_fv_empty_0063 h)

theorem nb090_wpp_notmem_1818 (A : Class) : (nb090_alpha_dummy_002 A) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_002, fv_syn_c1st] using (nb090_compact_fv_empty_0020 A)

theorem nb090_wpp_notmem_1819 (v : Var) : v ∉ ((syn_c1st)).fv := by
  simpa only [fv_syn_c1st] using (nb090_compact_fv_empty_0021 v)

theorem nb090_wpp_notmem_1820 (A : Class) : (nb090_alpha_dummy_001 A) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_001, fv_syn_c1st] using (nb090_compact_fv_empty_0022 A)

theorem nb090_wpp_notmem_1821 (u : Var) : u ∉ ((syn_c1st)).fv := by
  simpa only [fv_syn_c1st] using (nb090_compact_fv_empty_0023 u)

theorem nb090_wpp_notmem_1822 (A : Class) : (nb090_alpha_dummy_003 A) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_003, fv_syn_c1st] using (nb090_compact_fv_empty_0024 A)

theorem nb090_wpp_notmem_1823 (v : Var) (u : Var) (A : Class) (h : Var) : (nb090_alpha_dummy_004 v u A h) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_004, fv_syn_c1st] using (nb090_compact_fv_empty_0025 v u A h)

theorem nb090_compact_envfresh_0298 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1st)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_653 A) (nb090_alpha_dummy_654 u) (nb090_wpp_notmem_1804 A) (nb090_wpp_notmem_1805 u) (TEnvFresh.consFresh (nb090_alpha_dummy_655 A) (nb090_alpha_dummy_656 u) (nb090_wpp_notmem_1806 A) (nb090_wpp_notmem_1807 u) (TEnvFresh.consFresh (nb090_alpha_dummy_658 A) (nb090_alpha_dummy_660 u) (nb090_wpp_notmem_1808 A) (nb090_wpp_notmem_1809 u) (TEnvFresh.consFresh (nb090_alpha_dummy_657 A) (nb090_alpha_dummy_659 u) (nb090_wpp_notmem_1810 A) (nb090_wpp_notmem_1811 u) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1812 A) (nb090_wpp_notmem_1813 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1814 A) (nb090_wpp_notmem_1815 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_1816 A) (nb090_wpp_notmem_1817 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_1818 A) (nb090_wpp_notmem_1819 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_1820 A) (nb090_wpp_notmem_1821 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_1822 A) (nb090_wpp_notmem_1823 v u A h) (TEnvFresh.nil ((syn_c1st)).fv)))))))))))

noncomputable def nb090_wpp_refl_0298 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1st)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0298 v u A h)

theorem nb090_compact_fv_empty_0526 (A : Class) : (nb090_alpha_dummy_731 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1824 (A : Class) : (nb090_alpha_dummy_731 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_731, fv_syn_c1c] using (nb090_compact_fv_empty_0526 A)

theorem nb090_compact_fv_empty_0527 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_734 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1825 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_734 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_734, fv_syn_c1c] using (nb090_compact_fv_empty_0527 v u h)

theorem nb090_compact_fv_empty_0528 (A : Class) : (nb090_alpha_dummy_730 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1826 (A : Class) : (nb090_alpha_dummy_730 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_730, fv_syn_c1c] using (nb090_compact_fv_empty_0528 A)

theorem nb090_compact_fv_empty_0529 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_733 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1827 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_733 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_733, fv_syn_c1c] using (nb090_compact_fv_empty_0529 v u h)

theorem nb090_compact_fv_empty_0530 (A : Class) : (nb090_alpha_dummy_729 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1828 (A : Class) : (nb090_alpha_dummy_729 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_729, fv_syn_c1c] using (nb090_compact_fv_empty_0530 A)

theorem nb090_compact_fv_empty_0531 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_732 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1829 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_732 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_732, fv_syn_c1c] using (nb090_compact_fv_empty_0531 v u h)

theorem nb090_compact_fv_empty_0532 (A : Class) : (nb090_alpha_dummy_727 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1830 (A : Class) : (nb090_alpha_dummy_727 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_727, fv_syn_c1c] using (nb090_compact_fv_empty_0532 A)

theorem nb090_compact_fv_empty_0533 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_728 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1831 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_728 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_728, fv_syn_c1c] using (nb090_compact_fv_empty_0533 v u h)

theorem nb090_compact_fv_empty_0534 (A : Class) : (nb090_alpha_dummy_723 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1832 (A : Class) : (nb090_alpha_dummy_723 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_723, fv_syn_c1c] using (nb090_compact_fv_empty_0534 A)

theorem nb090_compact_fv_empty_0535 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_725 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1833 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_725 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_725, fv_syn_c1c] using (nb090_compact_fv_empty_0535 v u h)

theorem nb090_compact_fv_empty_0536 (A : Class) : (nb090_alpha_dummy_724 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1834 (A : Class) : (nb090_alpha_dummy_724 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_724, fv_syn_c1c] using (nb090_compact_fv_empty_0536 A)

theorem nb090_compact_fv_empty_0537 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_726 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1835 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_726 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_726, fv_syn_c1c] using (nb090_compact_fv_empty_0537 v u h)

theorem nb090_compact_fv_empty_0538 (A : Class) : (nb090_alpha_dummy_716 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1836 (A : Class) : (nb090_alpha_dummy_716 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_716, fv_syn_c1c] using (nb090_compact_fv_empty_0538 A)

theorem nb090_compact_fv_empty_0539 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_718 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1837 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_718 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_718, fv_syn_c1c] using (nb090_compact_fv_empty_0539 v u h)

theorem nb090_compact_fv_empty_0540 (A : Class) : (nb090_alpha_dummy_715 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1838 (A : Class) : (nb090_alpha_dummy_715 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_715, fv_syn_c1c] using (nb090_compact_fv_empty_0540 A)

theorem nb090_compact_fv_empty_0541 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_717 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1839 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_717 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_717, fv_syn_c1c] using (nb090_compact_fv_empty_0541 v u h)

theorem nb090_compact_fv_empty_0542 (A : Class) : (nb090_alpha_dummy_721 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1840 (A : Class) : (nb090_alpha_dummy_721 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_721, fv_syn_c1c] using (nb090_compact_fv_empty_0542 A)

theorem nb090_compact_fv_empty_0543 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_722 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1841 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_722 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_722, fv_syn_c1c] using (nb090_compact_fv_empty_0543 v u h)

theorem nb090_compact_fv_empty_0544 (A : Class) : (nb090_alpha_dummy_719 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1842 (A : Class) : (nb090_alpha_dummy_719 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_719, fv_syn_c1c] using (nb090_compact_fv_empty_0544 A)

theorem nb090_compact_fv_empty_0545 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_720 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1843 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_720 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_720, fv_syn_c1c] using (nb090_compact_fv_empty_0545 v u h)

theorem nb090_compact_fv_empty_0546 (A : Class) : (nb090_alpha_dummy_707 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1844 (A : Class) : (nb090_alpha_dummy_707 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_707, fv_syn_c1c] using (nb090_compact_fv_empty_0546 A)

theorem nb090_compact_fv_empty_0547 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_708 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1845 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_708 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_708, fv_syn_c1c] using (nb090_compact_fv_empty_0547 v u h)

theorem nb090_compact_fv_empty_0548 (A : Class) : (nb090_alpha_dummy_709 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1846 (A : Class) : (nb090_alpha_dummy_709 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_709, fv_syn_c1c] using (nb090_compact_fv_empty_0548 A)

theorem nb090_compact_fv_empty_0549 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_710 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1847 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_710 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_710, fv_syn_c1c] using (nb090_compact_fv_empty_0549 v u h)

theorem nb090_compact_fv_empty_0550 (A : Class) : (nb090_alpha_dummy_712 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1848 (A : Class) : (nb090_alpha_dummy_712 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_712, fv_syn_c1c] using (nb090_compact_fv_empty_0550 A)

theorem nb090_compact_fv_empty_0551 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_714 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1849 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_714 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_714, fv_syn_c1c] using (nb090_compact_fv_empty_0551 v u h)

theorem nb090_compact_fv_empty_0552 (A : Class) : (nb090_alpha_dummy_711 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1850 (A : Class) : (nb090_alpha_dummy_711 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_711, fv_syn_c1c] using (nb090_compact_fv_empty_0552 A)

theorem nb090_compact_fv_empty_0553 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_713 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1851 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_713 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_713, fv_syn_c1c] using (nb090_compact_fv_empty_0553 v u h)

theorem nb090_compact_fv_empty_0554 (A : Class) : (nb090_alpha_dummy_700 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1852 (A : Class) : (nb090_alpha_dummy_700 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_700, fv_syn_c1c] using (nb090_compact_fv_empty_0554 A)

theorem nb090_compact_fv_empty_0555 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_702 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1853 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_702 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_702, fv_syn_c1c] using (nb090_compact_fv_empty_0555 v u h)

theorem nb090_compact_fv_empty_0556 (A : Class) : (nb090_alpha_dummy_699 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1854 (A : Class) : (nb090_alpha_dummy_699 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_699, fv_syn_c1c] using (nb090_compact_fv_empty_0556 A)

theorem nb090_compact_fv_empty_0557 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_701 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1855 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_701 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_701, fv_syn_c1c] using (nb090_compact_fv_empty_0557 v u h)

theorem nb090_compact_fv_empty_0558 (A : Class) : (nb090_alpha_dummy_705 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1856 (A : Class) : (nb090_alpha_dummy_705 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_705, fv_syn_c1c] using (nb090_compact_fv_empty_0558 A)

theorem nb090_compact_fv_empty_0559 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_706 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1857 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_706 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_706, fv_syn_c1c] using (nb090_compact_fv_empty_0559 v u h)

theorem nb090_compact_fv_empty_0560 (A : Class) : (nb090_alpha_dummy_703 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1858 (A : Class) : (nb090_alpha_dummy_703 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_703, fv_syn_c1c] using (nb090_compact_fv_empty_0560 A)

theorem nb090_compact_fv_empty_0561 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_704 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1859 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_704 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_704, fv_syn_c1c] using (nb090_compact_fv_empty_0561 v u h)

theorem nb090_compact_envfresh_0299 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_731 A), (nb090_alpha_dummy_734 v u h)), ((nb090_alpha_dummy_730 A), (nb090_alpha_dummy_733 v u h)), ((nb090_alpha_dummy_729 A), (nb090_alpha_dummy_732 v u h)), ((nb090_alpha_dummy_727 A), (nb090_alpha_dummy_728 v u h)), ((nb090_alpha_dummy_723 A), (nb090_alpha_dummy_725 v u h)), ((nb090_alpha_dummy_724 A), (nb090_alpha_dummy_726 v u h)), ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_721 A), (nb090_alpha_dummy_722 v u h)), ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_731 A) (nb090_alpha_dummy_734 v u h) (nb090_wpp_notmem_1824 A) (nb090_wpp_notmem_1825 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_730 A) (nb090_alpha_dummy_733 v u h) (nb090_wpp_notmem_1826 A) (nb090_wpp_notmem_1827 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_729 A) (nb090_alpha_dummy_732 v u h) (nb090_wpp_notmem_1828 A) (nb090_wpp_notmem_1829 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_727 A) (nb090_alpha_dummy_728 v u h) (nb090_wpp_notmem_1830 A) (nb090_wpp_notmem_1831 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_723 A) (nb090_alpha_dummy_725 v u h) (nb090_wpp_notmem_1832 A) (nb090_wpp_notmem_1833 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_724 A) (nb090_alpha_dummy_726 v u h) (nb090_wpp_notmem_1834 A) (nb090_wpp_notmem_1835 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_716 A) (nb090_alpha_dummy_718 v u h) (nb090_wpp_notmem_1836 A) (nb090_wpp_notmem_1837 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_715 A) (nb090_alpha_dummy_717 v u h) (nb090_wpp_notmem_1838 A) (nb090_wpp_notmem_1839 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_721 A) (nb090_alpha_dummy_722 v u h) (nb090_wpp_notmem_1840 A) (nb090_wpp_notmem_1841 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_719 A) (nb090_alpha_dummy_720 v u h) (nb090_wpp_notmem_1842 A) (nb090_wpp_notmem_1843 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_707 A) (nb090_alpha_dummy_708 v u h) (nb090_wpp_notmem_1844 A) (nb090_wpp_notmem_1845 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_709 A) (nb090_alpha_dummy_710 v u h) (nb090_wpp_notmem_1846 A) (nb090_wpp_notmem_1847 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_712 A) (nb090_alpha_dummy_714 v u h) (nb090_wpp_notmem_1848 A) (nb090_wpp_notmem_1849 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_711 A) (nb090_alpha_dummy_713 v u h) (nb090_wpp_notmem_1850 A) (nb090_wpp_notmem_1851 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_700 A) (nb090_alpha_dummy_702 v u h) (nb090_wpp_notmem_1852 A) (nb090_wpp_notmem_1853 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_699 A) (nb090_alpha_dummy_701 v u h) (nb090_wpp_notmem_1854 A) (nb090_wpp_notmem_1855 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_705 A) (nb090_alpha_dummy_706 v u h) (nb090_wpp_notmem_1856 A) (nb090_wpp_notmem_1857 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_703 A) (nb090_alpha_dummy_704 v u h) (nb090_wpp_notmem_1858 A) (nb090_wpp_notmem_1859 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1598 A) (nb090_wpp_notmem_1599 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1588 A) (nb090_wpp_notmem_1589 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))))

noncomputable def nb090_wpp_refl_0299 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_731 A), (nb090_alpha_dummy_734 v u h)), ((nb090_alpha_dummy_730 A), (nb090_alpha_dummy_733 v u h)), ((nb090_alpha_dummy_729 A), (nb090_alpha_dummy_732 v u h)), ((nb090_alpha_dummy_727 A), (nb090_alpha_dummy_728 v u h)), ((nb090_alpha_dummy_723 A), (nb090_alpha_dummy_725 v u h)), ((nb090_alpha_dummy_724 A), (nb090_alpha_dummy_726 v u h)), ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_721 A), (nb090_alpha_dummy_722 v u h)), ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0299 v u A h)

theorem nb090_wpp_notmem_1860 (A : Class) : (nb090_alpha_dummy_731 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_731, fv_syn_c0] using (nb090_compact_fv_empty_0526 A)

theorem nb090_wpp_notmem_1861 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_734 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_734, fv_syn_c0] using (nb090_compact_fv_empty_0527 v u h)

theorem nb090_wpp_notmem_1862 (A : Class) : (nb090_alpha_dummy_730 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_730, fv_syn_c0] using (nb090_compact_fv_empty_0528 A)

theorem nb090_wpp_notmem_1863 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_733 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_733, fv_syn_c0] using (nb090_compact_fv_empty_0529 v u h)

theorem nb090_wpp_notmem_1864 (A : Class) : (nb090_alpha_dummy_729 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_729, fv_syn_c0] using (nb090_compact_fv_empty_0530 A)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
