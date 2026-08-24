import NAR4C090C001Part106

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

noncomputable def nb090_split_alpha_0085 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_618 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.neg (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))) (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_620 v u h)) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.neg (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0676 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0677 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0673 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0675 v u h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0650 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0651 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0650 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0651 v u h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0680 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0681 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0678 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0679 v u h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_618 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0654 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0655 v u h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0654 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0655 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0652 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0653 v u h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A), (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0287 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0658 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0659 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0656 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0657 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0662 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0663 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0660 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0661 v u h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0658 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0659 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0656 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0657 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0662 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0663 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0660 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0661 v u h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A), (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0288 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0666 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0667 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0664 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0665 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0666 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0667 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0664 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0665 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0670 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0671 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0668 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0669 v u h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0670 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0671 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0668 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0669 v u h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0652 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0653 v u h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0289 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0652 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0653 v u h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0652 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0653 v u h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0289 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0650 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0651 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0650 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0651 v u h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0680 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0681 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0678 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0679 v u h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_618 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0654 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0655 v u h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0654 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0655 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0652 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0653 v u h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A), (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0287 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0658 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0659 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0656 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0657 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0662 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0663 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0660 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0661 v u h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0658 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0659 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0656 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0657 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0662 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0663 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0660 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0661 v u h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A), (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0288 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0666 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0667 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0664 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0665 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0666 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0667 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0664 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0665 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0670 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0671 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0668 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0669 v u h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0670 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0671 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0668 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0669 v u h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0652 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0653 v u h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0289 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0652 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0653 v u h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0652 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0653 v u h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0289 v u A h)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0290 v u A h)))))))))))

theorem nb090_compact_fv_empty_0492 (A : Class) : (nb090_alpha_dummy_677 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1690 (A : Class) : (nb090_alpha_dummy_677 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_677, fv_syn_c1c] using (nb090_compact_fv_empty_0492 A)

theorem nb090_compact_fv_empty_0493 (u : Var) : (nb090_alpha_dummy_680 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1691 (u : Var) : (nb090_alpha_dummy_680 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_680, fv_syn_c1c] using (nb090_compact_fv_empty_0493 u)

theorem nb090_compact_fv_empty_0494 (A : Class) : (nb090_alpha_dummy_676 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1692 (A : Class) : (nb090_alpha_dummy_676 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_676, fv_syn_c1c] using (nb090_compact_fv_empty_0494 A)

theorem nb090_compact_fv_empty_0495 (u : Var) : (nb090_alpha_dummy_679 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1693 (u : Var) : (nb090_alpha_dummy_679 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_679, fv_syn_c1c] using (nb090_compact_fv_empty_0495 u)

theorem nb090_compact_fv_empty_0496 (A : Class) : (nb090_alpha_dummy_675 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1694 (A : Class) : (nb090_alpha_dummy_675 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_675, fv_syn_c1c] using (nb090_compact_fv_empty_0496 A)

theorem nb090_compact_fv_empty_0497 (u : Var) : (nb090_alpha_dummy_678 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1695 (u : Var) : (nb090_alpha_dummy_678 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_678, fv_syn_c1c] using (nb090_compact_fv_empty_0497 u)

theorem nb090_compact_fv_empty_0498 (A : Class) : (nb090_alpha_dummy_673 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1696 (A : Class) : (nb090_alpha_dummy_673 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_673, fv_syn_c1c] using (nb090_compact_fv_empty_0498 A)

theorem nb090_compact_fv_empty_0499 (u : Var) : (nb090_alpha_dummy_674 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1697 (u : Var) : (nb090_alpha_dummy_674 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_674, fv_syn_c1c] using (nb090_compact_fv_empty_0499 u)

theorem nb090_compact_fv_empty_0500 (A : Class) : (nb090_alpha_dummy_669 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1698 (A : Class) : (nb090_alpha_dummy_669 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_669, fv_syn_c1c] using (nb090_compact_fv_empty_0500 A)

theorem nb090_compact_fv_empty_0501 (u : Var) : (nb090_alpha_dummy_671 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1699 (u : Var) : (nb090_alpha_dummy_671 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_671, fv_syn_c1c] using (nb090_compact_fv_empty_0501 u)

theorem nb090_compact_fv_empty_0502 (A : Class) : (nb090_alpha_dummy_670 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1700 (A : Class) : (nb090_alpha_dummy_670 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_670, fv_syn_c1c] using (nb090_compact_fv_empty_0502 A)

theorem nb090_compact_fv_empty_0503 (u : Var) : (nb090_alpha_dummy_672 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1701 (u : Var) : (nb090_alpha_dummy_672 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_672, fv_syn_c1c] using (nb090_compact_fv_empty_0503 u)

theorem nb090_compact_fv_empty_0504 (A : Class) : (nb090_alpha_dummy_662 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1702 (A : Class) : (nb090_alpha_dummy_662 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_662, fv_syn_c1c] using (nb090_compact_fv_empty_0504 A)

theorem nb090_compact_fv_empty_0505 (u : Var) : (nb090_alpha_dummy_664 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1703 (u : Var) : (nb090_alpha_dummy_664 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_664, fv_syn_c1c] using (nb090_compact_fv_empty_0505 u)

theorem nb090_compact_fv_empty_0506 (A : Class) : (nb090_alpha_dummy_661 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1704 (A : Class) : (nb090_alpha_dummy_661 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_661, fv_syn_c1c] using (nb090_compact_fv_empty_0506 A)

theorem nb090_compact_fv_empty_0507 (u : Var) : (nb090_alpha_dummy_663 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1705 (u : Var) : (nb090_alpha_dummy_663 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_663, fv_syn_c1c] using (nb090_compact_fv_empty_0507 u)

theorem nb090_compact_fv_empty_0508 (A : Class) : (nb090_alpha_dummy_667 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1706 (A : Class) : (nb090_alpha_dummy_667 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_667, fv_syn_c1c] using (nb090_compact_fv_empty_0508 A)

theorem nb090_compact_fv_empty_0509 (u : Var) : (nb090_alpha_dummy_668 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1707 (u : Var) : (nb090_alpha_dummy_668 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_668, fv_syn_c1c] using (nb090_compact_fv_empty_0509 u)

theorem nb090_compact_fv_empty_0510 (A : Class) : (nb090_alpha_dummy_665 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1708 (A : Class) : (nb090_alpha_dummy_665 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_665, fv_syn_c1c] using (nb090_compact_fv_empty_0510 A)

theorem nb090_compact_fv_empty_0511 (u : Var) : (nb090_alpha_dummy_666 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1709 (u : Var) : (nb090_alpha_dummy_666 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_666, fv_syn_c1c] using (nb090_compact_fv_empty_0511 u)

theorem nb090_compact_fv_empty_0512 (A : Class) : (nb090_alpha_dummy_653 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1710 (A : Class) : (nb090_alpha_dummy_653 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_653, fv_syn_c1c] using (nb090_compact_fv_empty_0512 A)

theorem nb090_compact_fv_empty_0513 (u : Var) : (nb090_alpha_dummy_654 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1711 (u : Var) : (nb090_alpha_dummy_654 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_654, fv_syn_c1c] using (nb090_compact_fv_empty_0513 u)

theorem nb090_compact_fv_empty_0514 (A : Class) : (nb090_alpha_dummy_655 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1712 (A : Class) : (nb090_alpha_dummy_655 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_655, fv_syn_c1c] using (nb090_compact_fv_empty_0514 A)

theorem nb090_compact_fv_empty_0515 (u : Var) : (nb090_alpha_dummy_656 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1713 (u : Var) : (nb090_alpha_dummy_656 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_656, fv_syn_c1c] using (nb090_compact_fv_empty_0515 u)

theorem nb090_compact_fv_empty_0516 (A : Class) : (nb090_alpha_dummy_658 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1714 (A : Class) : (nb090_alpha_dummy_658 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_658, fv_syn_c1c] using (nb090_compact_fv_empty_0516 A)

theorem nb090_compact_fv_empty_0517 (u : Var) : (nb090_alpha_dummy_660 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1715 (u : Var) : (nb090_alpha_dummy_660 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_660, fv_syn_c1c] using (nb090_compact_fv_empty_0517 u)

theorem nb090_compact_fv_empty_0518 (A : Class) : (nb090_alpha_dummy_657 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1716 (A : Class) : (nb090_alpha_dummy_657 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_657, fv_syn_c1c] using (nb090_compact_fv_empty_0518 A)

theorem nb090_compact_fv_empty_0519 (u : Var) : (nb090_alpha_dummy_659 u) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1717 (u : Var) : (nb090_alpha_dummy_659 u) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_659, fv_syn_c1c] using (nb090_compact_fv_empty_0519 u)

theorem nb090_compact_envfresh_0291 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)), ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_677 A) (nb090_alpha_dummy_680 u) (nb090_wpp_notmem_1690 A) (nb090_wpp_notmem_1691 u) (TEnvFresh.consFresh (nb090_alpha_dummy_676 A) (nb090_alpha_dummy_679 u) (nb090_wpp_notmem_1692 A) (nb090_wpp_notmem_1693 u) (TEnvFresh.consFresh (nb090_alpha_dummy_675 A) (nb090_alpha_dummy_678 u) (nb090_wpp_notmem_1694 A) (nb090_wpp_notmem_1695 u) (TEnvFresh.consFresh (nb090_alpha_dummy_673 A) (nb090_alpha_dummy_674 u) (nb090_wpp_notmem_1696 A) (nb090_wpp_notmem_1697 u) (TEnvFresh.consFresh (nb090_alpha_dummy_669 A) (nb090_alpha_dummy_671 u) (nb090_wpp_notmem_1698 A) (nb090_wpp_notmem_1699 u) (TEnvFresh.consFresh (nb090_alpha_dummy_670 A) (nb090_alpha_dummy_672 u) (nb090_wpp_notmem_1700 A) (nb090_wpp_notmem_1701 u) (TEnvFresh.consFresh (nb090_alpha_dummy_662 A) (nb090_alpha_dummy_664 u) (nb090_wpp_notmem_1702 A) (nb090_wpp_notmem_1703 u) (TEnvFresh.consFresh (nb090_alpha_dummy_661 A) (nb090_alpha_dummy_663 u) (nb090_wpp_notmem_1704 A) (nb090_wpp_notmem_1705 u) (TEnvFresh.consFresh (nb090_alpha_dummy_667 A) (nb090_alpha_dummy_668 u) (nb090_wpp_notmem_1706 A) (nb090_wpp_notmem_1707 u) (TEnvFresh.consFresh (nb090_alpha_dummy_665 A) (nb090_alpha_dummy_666 u) (nb090_wpp_notmem_1708 A) (nb090_wpp_notmem_1709 u) (TEnvFresh.consFresh (nb090_alpha_dummy_653 A) (nb090_alpha_dummy_654 u) (nb090_wpp_notmem_1710 A) (nb090_wpp_notmem_1711 u) (TEnvFresh.consFresh (nb090_alpha_dummy_655 A) (nb090_alpha_dummy_656 u) (nb090_wpp_notmem_1712 A) (nb090_wpp_notmem_1713 u) (TEnvFresh.consFresh (nb090_alpha_dummy_658 A) (nb090_alpha_dummy_660 u) (nb090_wpp_notmem_1714 A) (nb090_wpp_notmem_1715 u) (TEnvFresh.consFresh (nb090_alpha_dummy_657 A) (nb090_alpha_dummy_659 u) (nb090_wpp_notmem_1716 A) (nb090_wpp_notmem_1717 u) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1598 A) (nb090_wpp_notmem_1599 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1588 A) (nb090_wpp_notmem_1589 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb090_wpp_refl_0291 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)), ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0291 v u A h)

theorem nb090_wpp_notmem_1718 (A : Class) : (nb090_alpha_dummy_677 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_677, fv_syn_c0] using (nb090_compact_fv_empty_0492 A)

theorem nb090_wpp_notmem_1719 (u : Var) : (nb090_alpha_dummy_680 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_680, fv_syn_c0] using (nb090_compact_fv_empty_0493 u)

theorem nb090_wpp_notmem_1720 (A : Class) : (nb090_alpha_dummy_676 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_676, fv_syn_c0] using (nb090_compact_fv_empty_0494 A)

theorem nb090_wpp_notmem_1721 (u : Var) : (nb090_alpha_dummy_679 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_679, fv_syn_c0] using (nb090_compact_fv_empty_0495 u)

theorem nb090_wpp_notmem_1722 (A : Class) : (nb090_alpha_dummy_675 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_675, fv_syn_c0] using (nb090_compact_fv_empty_0496 A)

theorem nb090_wpp_notmem_1723 (u : Var) : (nb090_alpha_dummy_678 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_678, fv_syn_c0] using (nb090_compact_fv_empty_0497 u)

theorem nb090_wpp_notmem_1724 (A : Class) : (nb090_alpha_dummy_673 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_673, fv_syn_c0] using (nb090_compact_fv_empty_0498 A)

theorem nb090_wpp_notmem_1725 (u : Var) : (nb090_alpha_dummy_674 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_674, fv_syn_c0] using (nb090_compact_fv_empty_0499 u)

theorem nb090_wpp_notmem_1726 (A : Class) : (nb090_alpha_dummy_669 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_669, fv_syn_c0] using (nb090_compact_fv_empty_0500 A)

theorem nb090_wpp_notmem_1727 (u : Var) : (nb090_alpha_dummy_671 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_671, fv_syn_c0] using (nb090_compact_fv_empty_0501 u)

theorem nb090_wpp_notmem_1728 (A : Class) : (nb090_alpha_dummy_670 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_670, fv_syn_c0] using (nb090_compact_fv_empty_0502 A)

theorem nb090_wpp_notmem_1729 (u : Var) : (nb090_alpha_dummy_672 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_672, fv_syn_c0] using (nb090_compact_fv_empty_0503 u)

theorem nb090_wpp_notmem_1730 (A : Class) : (nb090_alpha_dummy_662 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_662, fv_syn_c0] using (nb090_compact_fv_empty_0504 A)

theorem nb090_wpp_notmem_1731 (u : Var) : (nb090_alpha_dummy_664 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_664, fv_syn_c0] using (nb090_compact_fv_empty_0505 u)

theorem nb090_wpp_notmem_1732 (A : Class) : (nb090_alpha_dummy_661 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_661, fv_syn_c0] using (nb090_compact_fv_empty_0506 A)

theorem nb090_wpp_notmem_1733 (u : Var) : (nb090_alpha_dummy_663 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_663, fv_syn_c0] using (nb090_compact_fv_empty_0507 u)

theorem nb090_wpp_notmem_1734 (A : Class) : (nb090_alpha_dummy_667 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_667, fv_syn_c0] using (nb090_compact_fv_empty_0508 A)

theorem nb090_wpp_notmem_1735 (u : Var) : (nb090_alpha_dummy_668 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_668, fv_syn_c0] using (nb090_compact_fv_empty_0509 u)

theorem nb090_wpp_notmem_1736 (A : Class) : (nb090_alpha_dummy_665 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_665, fv_syn_c0] using (nb090_compact_fv_empty_0510 A)

theorem nb090_wpp_notmem_1737 (u : Var) : (nb090_alpha_dummy_666 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_666, fv_syn_c0] using (nb090_compact_fv_empty_0511 u)

theorem nb090_wpp_notmem_1738 (A : Class) : (nb090_alpha_dummy_653 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_653, fv_syn_c0] using (nb090_compact_fv_empty_0512 A)

theorem nb090_wpp_notmem_1739 (u : Var) : (nb090_alpha_dummy_654 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_654, fv_syn_c0] using (nb090_compact_fv_empty_0513 u)

theorem nb090_wpp_notmem_1740 (A : Class) : (nb090_alpha_dummy_655 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_655, fv_syn_c0] using (nb090_compact_fv_empty_0514 A)

theorem nb090_wpp_notmem_1741 (u : Var) : (nb090_alpha_dummy_656 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_656, fv_syn_c0] using (nb090_compact_fv_empty_0515 u)

theorem nb090_wpp_notmem_1742 (A : Class) : (nb090_alpha_dummy_658 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_658, fv_syn_c0] using (nb090_compact_fv_empty_0516 A)

theorem nb090_wpp_notmem_1743 (u : Var) : (nb090_alpha_dummy_660 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_660, fv_syn_c0] using (nb090_compact_fv_empty_0517 u)

theorem nb090_wpp_notmem_1744 (A : Class) : (nb090_alpha_dummy_657 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_657, fv_syn_c0] using (nb090_compact_fv_empty_0518 A)

theorem nb090_wpp_notmem_1745 (u : Var) : (nb090_alpha_dummy_659 u) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_659, fv_syn_c0] using (nb090_compact_fv_empty_0519 u)

theorem nb090_compact_envfresh_0292 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)), ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_677 A) (nb090_alpha_dummy_680 u) (nb090_wpp_notmem_1718 A) (nb090_wpp_notmem_1719 u) (TEnvFresh.consFresh (nb090_alpha_dummy_676 A) (nb090_alpha_dummy_679 u) (nb090_wpp_notmem_1720 A) (nb090_wpp_notmem_1721 u) (TEnvFresh.consFresh (nb090_alpha_dummy_675 A) (nb090_alpha_dummy_678 u) (nb090_wpp_notmem_1722 A) (nb090_wpp_notmem_1723 u) (TEnvFresh.consFresh (nb090_alpha_dummy_673 A) (nb090_alpha_dummy_674 u) (nb090_wpp_notmem_1724 A) (nb090_wpp_notmem_1725 u) (TEnvFresh.consFresh (nb090_alpha_dummy_669 A) (nb090_alpha_dummy_671 u) (nb090_wpp_notmem_1726 A) (nb090_wpp_notmem_1727 u) (TEnvFresh.consFresh (nb090_alpha_dummy_670 A) (nb090_alpha_dummy_672 u) (nb090_wpp_notmem_1728 A) (nb090_wpp_notmem_1729 u) (TEnvFresh.consFresh (nb090_alpha_dummy_662 A) (nb090_alpha_dummy_664 u) (nb090_wpp_notmem_1730 A) (nb090_wpp_notmem_1731 u) (TEnvFresh.consFresh (nb090_alpha_dummy_661 A) (nb090_alpha_dummy_663 u) (nb090_wpp_notmem_1732 A) (nb090_wpp_notmem_1733 u) (TEnvFresh.consFresh (nb090_alpha_dummy_667 A) (nb090_alpha_dummy_668 u) (nb090_wpp_notmem_1734 A) (nb090_wpp_notmem_1735 u) (TEnvFresh.consFresh (nb090_alpha_dummy_665 A) (nb090_alpha_dummy_666 u) (nb090_wpp_notmem_1736 A) (nb090_wpp_notmem_1737 u) (TEnvFresh.consFresh (nb090_alpha_dummy_653 A) (nb090_alpha_dummy_654 u) (nb090_wpp_notmem_1738 A) (nb090_wpp_notmem_1739 u) (TEnvFresh.consFresh (nb090_alpha_dummy_655 A) (nb090_alpha_dummy_656 u) (nb090_wpp_notmem_1740 A) (nb090_wpp_notmem_1741 u) (TEnvFresh.consFresh (nb090_alpha_dummy_658 A) (nb090_alpha_dummy_660 u) (nb090_wpp_notmem_1742 A) (nb090_wpp_notmem_1743 u) (TEnvFresh.consFresh (nb090_alpha_dummy_657 A) (nb090_alpha_dummy_659 u) (nb090_wpp_notmem_1744 A) (nb090_wpp_notmem_1745 u) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1600 A) (nb090_wpp_notmem_1601 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1590 A) (nb090_wpp_notmem_1591 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb090_wpp_refl_0292 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)), ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0292 v u A h)

theorem nb090_wpp_notmem_1746 (A : Class) : (nb090_alpha_dummy_673 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_673, fv_syn_cnnc] using (nb090_compact_fv_empty_0498 A)

theorem nb090_wpp_notmem_1747 (u : Var) : (nb090_alpha_dummy_674 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_674, fv_syn_cnnc] using (nb090_compact_fv_empty_0499 u)

theorem nb090_wpp_notmem_1748 (A : Class) : (nb090_alpha_dummy_669 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_669, fv_syn_cnnc] using (nb090_compact_fv_empty_0500 A)

theorem nb090_wpp_notmem_1749 (u : Var) : (nb090_alpha_dummy_671 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_671, fv_syn_cnnc] using (nb090_compact_fv_empty_0501 u)

theorem nb090_wpp_notmem_1750 (A : Class) : (nb090_alpha_dummy_670 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_670, fv_syn_cnnc] using (nb090_compact_fv_empty_0502 A)

theorem nb090_wpp_notmem_1751 (u : Var) : (nb090_alpha_dummy_672 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_672, fv_syn_cnnc] using (nb090_compact_fv_empty_0503 u)

theorem nb090_wpp_notmem_1752 (A : Class) : (nb090_alpha_dummy_662 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_662, fv_syn_cnnc] using (nb090_compact_fv_empty_0504 A)

theorem nb090_wpp_notmem_1753 (u : Var) : (nb090_alpha_dummy_664 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_664, fv_syn_cnnc] using (nb090_compact_fv_empty_0505 u)

theorem nb090_wpp_notmem_1754 (A : Class) : (nb090_alpha_dummy_661 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_661, fv_syn_cnnc] using (nb090_compact_fv_empty_0506 A)

theorem nb090_wpp_notmem_1755 (u : Var) : (nb090_alpha_dummy_663 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_663, fv_syn_cnnc] using (nb090_compact_fv_empty_0507 u)

theorem nb090_wpp_notmem_1756 (A : Class) : (nb090_alpha_dummy_667 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_667, fv_syn_cnnc] using (nb090_compact_fv_empty_0508 A)

theorem nb090_wpp_notmem_1757 (u : Var) : (nb090_alpha_dummy_668 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_668, fv_syn_cnnc] using (nb090_compact_fv_empty_0509 u)

theorem nb090_wpp_notmem_1758 (A : Class) : (nb090_alpha_dummy_665 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_665, fv_syn_cnnc] using (nb090_compact_fv_empty_0510 A)

theorem nb090_wpp_notmem_1759 (u : Var) : (nb090_alpha_dummy_666 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_666, fv_syn_cnnc] using (nb090_compact_fv_empty_0511 u)

theorem nb090_wpp_notmem_1760 (A : Class) : (nb090_alpha_dummy_653 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_653, fv_syn_cnnc] using (nb090_compact_fv_empty_0512 A)

theorem nb090_wpp_notmem_1761 (u : Var) : (nb090_alpha_dummy_654 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_654, fv_syn_cnnc] using (nb090_compact_fv_empty_0513 u)

theorem nb090_wpp_notmem_1762 (A : Class) : (nb090_alpha_dummy_655 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_655, fv_syn_cnnc] using (nb090_compact_fv_empty_0514 A)

theorem nb090_wpp_notmem_1763 (u : Var) : (nb090_alpha_dummy_656 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_656, fv_syn_cnnc] using (nb090_compact_fv_empty_0515 u)

theorem nb090_wpp_notmem_1764 (A : Class) : (nb090_alpha_dummy_658 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_658, fv_syn_cnnc] using (nb090_compact_fv_empty_0516 A)

theorem nb090_wpp_notmem_1765 (u : Var) : (nb090_alpha_dummy_660 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_660, fv_syn_cnnc] using (nb090_compact_fv_empty_0517 u)

theorem nb090_wpp_notmem_1766 (A : Class) : (nb090_alpha_dummy_657 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_657, fv_syn_cnnc] using (nb090_compact_fv_empty_0518 A)

theorem nb090_wpp_notmem_1767 (u : Var) : (nb090_alpha_dummy_659 u) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_659, fv_syn_cnnc] using (nb090_compact_fv_empty_0519 u)

theorem nb090_compact_envfresh_0293 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_673 A) (nb090_alpha_dummy_674 u) (nb090_wpp_notmem_1746 A) (nb090_wpp_notmem_1747 u) (TEnvFresh.consFresh (nb090_alpha_dummy_669 A) (nb090_alpha_dummy_671 u) (nb090_wpp_notmem_1748 A) (nb090_wpp_notmem_1749 u) (TEnvFresh.consFresh (nb090_alpha_dummy_670 A) (nb090_alpha_dummy_672 u) (nb090_wpp_notmem_1750 A) (nb090_wpp_notmem_1751 u) (TEnvFresh.consFresh (nb090_alpha_dummy_662 A) (nb090_alpha_dummy_664 u) (nb090_wpp_notmem_1752 A) (nb090_wpp_notmem_1753 u) (TEnvFresh.consFresh (nb090_alpha_dummy_661 A) (nb090_alpha_dummy_663 u) (nb090_wpp_notmem_1754 A) (nb090_wpp_notmem_1755 u) (TEnvFresh.consFresh (nb090_alpha_dummy_667 A) (nb090_alpha_dummy_668 u) (nb090_wpp_notmem_1756 A) (nb090_wpp_notmem_1757 u) (TEnvFresh.consFresh (nb090_alpha_dummy_665 A) (nb090_alpha_dummy_666 u) (nb090_wpp_notmem_1758 A) (nb090_wpp_notmem_1759 u) (TEnvFresh.consFresh (nb090_alpha_dummy_653 A) (nb090_alpha_dummy_654 u) (nb090_wpp_notmem_1760 A) (nb090_wpp_notmem_1761 u) (TEnvFresh.consFresh (nb090_alpha_dummy_655 A) (nb090_alpha_dummy_656 u) (nb090_wpp_notmem_1762 A) (nb090_wpp_notmem_1763 u) (TEnvFresh.consFresh (nb090_alpha_dummy_658 A) (nb090_alpha_dummy_660 u) (nb090_wpp_notmem_1764 A) (nb090_wpp_notmem_1765 u) (TEnvFresh.consFresh (nb090_alpha_dummy_657 A) (nb090_alpha_dummy_659 u) (nb090_wpp_notmem_1766 A) (nb090_wpp_notmem_1767 u) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1602 A) (nb090_wpp_notmem_1603 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1592 A) (nb090_wpp_notmem_1593 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb090_wpp_refl_0293 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0293 v u A h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
