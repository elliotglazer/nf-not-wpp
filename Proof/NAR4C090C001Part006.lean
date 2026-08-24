import NAR4C090C001Part005

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

noncomputable def nb090_alpha_dummy_750 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_751 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_709 A))).fv) 0)

noncomputable def nb090_alpha_dummy_752 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_710 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_753 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_700 A))).fv) 0)

noncomputable def nb090_alpha_dummy_754 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_700 A))).fv) 1)

noncomputable def nb090_alpha_dummy_755 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_756 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) 1)

noncomputable def nb090_alpha_dummy_757 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_753 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_753 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_753 A))).fv) 0)

noncomputable def nb090_alpha_dummy_758 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_755 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_759 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_760 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_761 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_762 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_763 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_764 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_765 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_766 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h)) (Class.cv (nb090_alpha_dummy_764 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h)) (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_767 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) 0)

noncomputable def nb090_alpha_dummy_768 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_769 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_760 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_761 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_770 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_763 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_771 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_760 A))).fv) 0)

noncomputable def nb090_alpha_dummy_772 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_763 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_773 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_761 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) 0)

noncomputable def nb090_alpha_dummy_774 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_764 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_775 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A))) (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_776 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h) (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_777 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) 0)

noncomputable def nb090_alpha_dummy_778 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_779 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_777 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_780 (v : Var) (u : Var) (h : Var) : Var := (freshVar (({(nb090_alpha_dummy_778 v u h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_781 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) 0)

noncomputable def nb090_alpha_dummy_782 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) 1)

noncomputable def nb090_alpha_dummy_783 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) 0)

noncomputable def nb090_alpha_dummy_784 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) 1)

noncomputable def nb090_alpha_dummy_785 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) 0)

noncomputable def nb090_alpha_dummy_786 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) 1)

noncomputable def nb090_alpha_dummy_787 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_788 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) 1)

noncomputable def nb090_alpha_dummy_789 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_790 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_791 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_792 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv) 0)

noncomputable def nb090_alpha_dummy_793 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_786 A))).fv) 0)

noncomputable def nb090_alpha_dummy_794 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_786 A))).fv) 1)

noncomputable def nb090_alpha_dummy_795 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_796 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) 1)

noncomputable def nb090_alpha_dummy_797 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_793 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_793 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_793 A))).fv) 0)

noncomputable def nb090_alpha_dummy_798 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_795 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_799 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_800 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_801 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_802 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_803 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_804 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_805 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_806 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h)) (Class.cv (nb090_alpha_dummy_804 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h)) (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_807 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) 0)

noncomputable def nb090_alpha_dummy_808 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_809 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_800 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_801 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_810 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_803 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_811 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_800 A))).fv) 0)

noncomputable def nb090_alpha_dummy_812 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_803 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_813 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_801 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) 0)

noncomputable def nb090_alpha_dummy_814 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_804 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_815 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_816 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_817 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_818 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_819 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_820 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_821 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_779 A))).fv) 0)

noncomputable def nb090_alpha_dummy_822 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_780 v u h))).fv) 0)

noncomputable def nb090_alpha_dummy_823 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_824 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_825 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_826 (v : Var) (u : Var) (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv) 0)

noncomputable def nb090_alpha_dummy_827 (A : Class) : Var := (freshVar (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0)

noncomputable def nb090_alpha_dummy_828 (v : Var) : Var := (freshVar (((syn_c1st)).fv ∪ ((Class.cv v)).fv) 0)

noncomputable def nb090_alpha_dummy_829 (A : Class) : Var := (freshVar (({(nb090_alpha_dummy_827 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_830 (v : Var) : Var := (freshVar (({(nb090_alpha_dummy_828 v)} : Finset Var) ∪ ((syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))).fv) 0)

noncomputable def nb090_alpha_dummy_831 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) 0)

noncomputable def nb090_alpha_dummy_832 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) 1)

noncomputable def nb090_alpha_dummy_833 (v : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v) (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) 0)

noncomputable def nb090_alpha_dummy_834 (v : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v) (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) 1)

noncomputable def nb090_alpha_dummy_835 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) 0)

noncomputable def nb090_alpha_dummy_836 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) 1)

noncomputable def nb090_alpha_dummy_837 (v : Var) : Var := (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) 0)

noncomputable def nb090_alpha_dummy_838 (v : Var) : Var := (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) 1)

noncomputable def nb090_alpha_dummy_839 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_840 (v : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb090_alpha_dummy_841 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv) 0)

noncomputable def nb090_alpha_dummy_842 (v : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv) 0)

noncomputable def nb090_alpha_dummy_843 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_836 A))).fv) 0)

noncomputable def nb090_alpha_dummy_844 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_836 A))).fv) 1)

noncomputable def nb090_alpha_dummy_845 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_838 v))).fv) 0)

noncomputable def nb090_alpha_dummy_846 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_838 v))).fv) 1)

noncomputable def nb090_alpha_dummy_847 (A : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_843 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_843 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_843 A))).fv) 0)

noncomputable def nb090_alpha_dummy_848 (v : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_845 v)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_845 v)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_845 v))).fv) 0)

noncomputable def nb090_alpha_dummy_849 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_850 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_851 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_852 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb090_alpha_dummy_853 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb090_alpha_dummy_854 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb090_alpha_dummy_855 (A : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_856 (v : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv) 0)

noncomputable def nb090_alpha_dummy_857 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) 0)

noncomputable def nb090_alpha_dummy_858 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) 0)

noncomputable def nb090_alpha_dummy_859 (A : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_850 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_851 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_860 (v : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_853 v)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_854 v)))).fv) 0)

noncomputable def nb090_alpha_dummy_861 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_850 A))).fv) 0)

noncomputable def nb090_alpha_dummy_862 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_853 v))).fv) 0)

noncomputable def nb090_alpha_dummy_863 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_851 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) 0)

noncomputable def nb090_alpha_dummy_864 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_854 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) 0)

noncomputable def nb090_alpha_dummy_865 (A : Class) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_866 (v : Var) : Var := (freshVar (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb090_alpha_dummy_867 (A : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_868 (v : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb090_alpha_dummy_869 (A : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv) 0)

noncomputable def nb090_alpha_dummy_870 (v : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv) 0)

noncomputable def nb090_alpha_dummy_871 (A : Class) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_829 A))).fv) 0)

noncomputable def nb090_alpha_dummy_872 (v : Var) : Var := (freshVar (((Class.cv (nb090_alpha_dummy_830 v))).fv) 0)

theorem nb090_fresh_000 (A : Class) : (nb090_alpha_dummy_011 A) ∉ (((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_011] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv) 0

theorem nb090_fresh_001 (A : Class) : (nb090_alpha_dummy_035 A) ∉ (((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_035] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_002 (v : Var) (u : Var) : (nb090_alpha_dummy_012 v u) ∉ (((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv) := by
  simpa only [nb090_alpha_dummy_012] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv) 0

theorem nb090_fresh_003 (v : Var) (u : Var) : (nb090_alpha_dummy_036 v u) ∉ (((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_036] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_004 (A : Class) : (nb090_alpha_dummy_063 A) ∉ (((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_063] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv) 0

theorem nb090_fresh_005 (A : Class) : (nb090_alpha_dummy_087 A) ∉ (((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_087] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_006 (h : Var) : (nb090_alpha_dummy_064 h) ∉ (((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv) := by
  simpa only [nb090_alpha_dummy_064] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv) 0

theorem nb090_fresh_007 (h : Var) : (nb090_alpha_dummy_088 h) ∉ (((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_088] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_008 (A : Class) : (nb090_alpha_dummy_099 A) ∉ (((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_099] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv) 0

theorem nb090_fresh_009 (A : Class) : (nb090_alpha_dummy_123 A) ∉ (((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_123] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A) (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_010 (h : Var) : (nb090_alpha_dummy_100 h) ∉ (((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv) := by
  simpa only [nb090_alpha_dummy_100] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv) 0

theorem nb090_fresh_011 (h : Var) : (nb090_alpha_dummy_124 h) ∉ (((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_124] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h) (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_012 (A : Class) : (nb090_alpha_dummy_141 A) ∉ (((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_141] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv) 0

theorem nb090_fresh_013 (A : Class) : (nb090_alpha_dummy_165 A) ∉ (((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_165] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A) (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_014 (h : Var) : (nb090_alpha_dummy_142 h) ∉ (((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv) := by
  simpa only [nb090_alpha_dummy_142] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv) 0

theorem nb090_fresh_015 (h : Var) : (nb090_alpha_dummy_166 h) ∉ (((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_166] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h) (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_016 (A : Class) : (nb090_alpha_dummy_201 A) ∉ (((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_201] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_017 (A : Class) : (nb090_alpha_dummy_177 A) ∉ (((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_177] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A) (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv) 0

theorem nb090_fresh_018 (h : Var) : (nb090_alpha_dummy_202 h) ∉ (((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_202] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_019 (h : Var) : (nb090_alpha_dummy_178 h) ∉ (((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv) := by
  simpa only [nb090_alpha_dummy_178] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h) (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv) 0

theorem nb090_fresh_020 (A : Class) : (nb090_alpha_dummy_237 A) ∉ (((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_237] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_021 (A : Class) : (nb090_alpha_dummy_213 A) ∉ (((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_213] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A) (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv) 0

theorem nb090_fresh_022 (h : Var) : (nb090_alpha_dummy_238 h) ∉ (((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_238] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_023 (h : Var) : (nb090_alpha_dummy_214 h) ∉ (((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv) := by
  simpa only [nb090_alpha_dummy_214] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h) (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv) 0

theorem nb090_fresh_024 (A : Class) : (nb090_alpha_dummy_277 A) ∉ (((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_277] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_025 (A : Class) : (nb090_alpha_dummy_253 A) ∉ (((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_253] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv) 0

theorem nb090_fresh_026 (h : Var) : (nb090_alpha_dummy_278 h) ∉ (((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_278] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))) (syn_csn (syn_c0c))))))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
