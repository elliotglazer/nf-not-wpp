import NAR4C078C001Part005

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

noncomputable def nb078_alpha_dummy_750 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) 0)

noncomputable def nb078_alpha_dummy_751 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_742)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_743)))).fv) 0)

noncomputable def nb078_alpha_dummy_752 (g : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_745 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_746 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_753 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_742))).fv) 0)

noncomputable def nb078_alpha_dummy_754 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_745 g))).fv) 0)

noncomputable def nb078_alpha_dummy_755 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_743))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) 0)

noncomputable def nb078_alpha_dummy_756 (g : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_746 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) 0)

noncomputable def nb078_alpha_dummy_757 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_758 (g : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_759 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_728))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_760 (g : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_761 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv) 0)

noncomputable def nb078_alpha_dummy_762 (g : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv) 0)

noncomputable def nb078_alpha_dummy_763 : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv) 0)

noncomputable def nb078_alpha_dummy_764 (h : Var) : Var := (freshVar (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) 0)

noncomputable def nb078_alpha_dummy_765 : Var := (freshVar (((syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb078_alpha_dummy_766 (h : Var) : Var := (freshVar (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb078_alpha_dummy_767 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 0)

noncomputable def nb078_alpha_dummy_768 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 1)

noncomputable def nb078_alpha_dummy_769 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 2)

noncomputable def nb078_alpha_dummy_770 (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 0)

noncomputable def nb078_alpha_dummy_771 (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 1)

noncomputable def nb078_alpha_dummy_772 (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 2)

noncomputable def nb078_alpha_dummy_773 : Var := (freshVar (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv) 0)

noncomputable def nb078_alpha_dummy_774 (h : Var) : Var := (freshVar (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_772 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_771 h)))))).fv) 0)

noncomputable def nb078_alpha_dummy_775 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 0)

noncomputable def nb078_alpha_dummy_776 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 1)

noncomputable def nb078_alpha_dummy_777 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) 0)

noncomputable def nb078_alpha_dummy_778 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) 1)

noncomputable def nb078_alpha_dummy_779 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cphi (Class.cv (nb078_alpha_dummy_776)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_780 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_781 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv) 0)

noncomputable def nb078_alpha_dummy_782 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_783 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_776))).fv) 0)

noncomputable def nb078_alpha_dummy_784 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_776))).fv) 1)

noncomputable def nb078_alpha_dummy_785 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_778 h))).fv) 0)

noncomputable def nb078_alpha_dummy_786 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_778 h))).fv) 1)

noncomputable def nb078_alpha_dummy_787 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_783)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_783)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_783))).fv) 0)

noncomputable def nb078_alpha_dummy_788 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_785 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_785 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_785 h))).fv) 0)

noncomputable def nb078_alpha_dummy_789 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_790 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_791 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_792 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_793 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_794 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_795 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv) 0)

noncomputable def nb078_alpha_dummy_796 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_797 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) 0)

noncomputable def nb078_alpha_dummy_798 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) 0)

noncomputable def nb078_alpha_dummy_799 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_790)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_791)))).fv) 0)

noncomputable def nb078_alpha_dummy_800 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_793 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_794 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_801 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_790))).fv) 0)

noncomputable def nb078_alpha_dummy_802 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_793 h))).fv) 0)

noncomputable def nb078_alpha_dummy_803 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_791))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) 0)

noncomputable def nb078_alpha_dummy_804 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_794 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) 0)

noncomputable def nb078_alpha_dummy_805 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_806 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_807 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_776))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_808 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_809 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv) 0)

noncomputable def nb078_alpha_dummy_810 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_811 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) 0)

noncomputable def nb078_alpha_dummy_812 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) 1)

noncomputable def nb078_alpha_dummy_813 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) 0)

noncomputable def nb078_alpha_dummy_814 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) 1)

noncomputable def nb078_alpha_dummy_815 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_816 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_817 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv) 0)

noncomputable def nb078_alpha_dummy_818 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_819 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_812))).fv) 0)

noncomputable def nb078_alpha_dummy_820 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_812))).fv) 1)

noncomputable def nb078_alpha_dummy_821 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_814 h))).fv) 0)

noncomputable def nb078_alpha_dummy_822 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_814 h))).fv) 1)

noncomputable def nb078_alpha_dummy_823 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_819)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_819)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_819))).fv) 0)

noncomputable def nb078_alpha_dummy_824 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_821 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_821 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_821 h))).fv) 0)

noncomputable def nb078_alpha_dummy_825 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_826 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_827 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_828 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_829 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_830 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_831 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv) 0)

noncomputable def nb078_alpha_dummy_832 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_833 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) 0)

noncomputable def nb078_alpha_dummy_834 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) 0)

noncomputable def nb078_alpha_dummy_835 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_826)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_827)))).fv) 0)

noncomputable def nb078_alpha_dummy_836 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_829 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_830 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_837 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_826))).fv) 0)

noncomputable def nb078_alpha_dummy_838 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_829 h))).fv) 0)

noncomputable def nb078_alpha_dummy_839 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_827))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) 0)

noncomputable def nb078_alpha_dummy_840 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_830 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) 0)

noncomputable def nb078_alpha_dummy_841 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_842 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_843 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_812))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_844 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_845 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv) 0)

noncomputable def nb078_alpha_dummy_846 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_847 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv) 0)

noncomputable def nb078_alpha_dummy_848 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv) 1)

noncomputable def nb078_alpha_dummy_849 (h : Var) : Var := (freshVar (((Class.cv h)).fv) 0)

noncomputable def nb078_alpha_dummy_850 (h : Var) : Var := (freshVar (((Class.cv h)).fv) 1)

noncomputable def nb078_alpha_dummy_851 : Var := (freshVar (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_847)))).fv) 0)

noncomputable def nb078_alpha_dummy_852 (h : Var) : Var := (freshVar (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_849 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_853 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) 0)

noncomputable def nb078_alpha_dummy_854 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) 1)

noncomputable def nb078_alpha_dummy_855 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) 0)

noncomputable def nb078_alpha_dummy_856 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) 1)

noncomputable def nb078_alpha_dummy_857 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_858 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_859 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv) 0)

noncomputable def nb078_alpha_dummy_860 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_861 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_854))).fv) 0)

noncomputable def nb078_alpha_dummy_862 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_854))).fv) 1)

noncomputable def nb078_alpha_dummy_863 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_856 h))).fv) 0)

noncomputable def nb078_alpha_dummy_864 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_856 h))).fv) 1)

noncomputable def nb078_alpha_dummy_865 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_861)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_861)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_861))).fv) 0)

noncomputable def nb078_alpha_dummy_866 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_863 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_863 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_863 h))).fv) 0)

noncomputable def nb078_alpha_dummy_867 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_868 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_869 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_870 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_871 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_872 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_873 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv) 0)

noncomputable def nb078_alpha_dummy_874 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_875 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) 0)

noncomputable def nb078_alpha_dummy_876 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) 0)

noncomputable def nb078_alpha_dummy_877 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_868)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_869)))).fv) 0)

noncomputable def nb078_alpha_dummy_878 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_871 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_872 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_879 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_868))).fv) 0)

noncomputable def nb078_alpha_dummy_880 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_871 h))).fv) 0)

noncomputable def nb078_alpha_dummy_881 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_869))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) 0)

noncomputable def nb078_alpha_dummy_882 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_872 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) 0)

noncomputable def nb078_alpha_dummy_883 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_884 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_885 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_854))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_886 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_887 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv) 0)

noncomputable def nb078_alpha_dummy_888 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_889 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) 0)

noncomputable def nb078_alpha_dummy_890 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) 1)

noncomputable def nb078_alpha_dummy_891 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) 0)

noncomputable def nb078_alpha_dummy_892 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) 1)

noncomputable def nb078_alpha_dummy_893 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_894 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_895 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv) 0)

noncomputable def nb078_alpha_dummy_896 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_897 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_890))).fv) 0)

noncomputable def nb078_alpha_dummy_898 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_890))).fv) 1)

noncomputable def nb078_alpha_dummy_899 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_892 h))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
