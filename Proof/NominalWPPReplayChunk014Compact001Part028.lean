import WPPCompactSourceSyntax
import WPPCompactSyntaxFVExplicit
import CompactSyntaxFV
import CoreFVSimp
import NominalSubstitutionLemmas
import NominalDefinitionRefl
import NominalDfEu
import NominalAlphaRepairedDfNfc001
import NominalAlphaRepairedBase001003V
import NominalAlphaRepairedBase001004Csb
import NominalAlphaRepairedBase001005Nin
import NominalAlphaRepairedBase001006If
import NominalAlphaRepairedBase001007Pw
import NominalAlphaRepairedBase001008Sn
import NominalAlphaRepairedBase001009Uni
import NominalAlphaRepairedBase001010Int
import NominalAlphaRepairedBase001011Iun
import NominalAlphaRepairedBase001012Leaf1c
import NominalAlphaRepairedBase001013Xpk
import NominalAlphaRepairedBase001014Cnvk
import NominalAlphaRepairedBase001015Ins2k
import NominalAlphaRepairedBase001016Ins3k
import NominalAlphaRepairedBase001017Imak
import NominalAlphaRepairedBase001018P6
import NominalAlphaRepairedBase001019Sik
import NominalAlphaRepairedBase001020Ssetk
import NominalAlphaRepairedBase001021Idk
import NominalAlphaRepairedBase001022Iota
import NominalAlphaRepairedBase001023Addc
import NominalAlphaRepairedBase001024Nnc
import NominalAlphaRepairedBase001025Lefin
import NominalAlphaRepairedBase001026Ltfin
import NominalAlphaRepairedBase001027Ncfin
import NominalAlphaRepairedBase001028Tfin
import NominalAlphaRepairedBase001029Evenfin
import NominalAlphaRepairedBase001030Oddfin
import NominalAlphaRepairedBase001031Sfin
import NominalAlphaRepairedBase001032Spfin
import NominalAlphaRepairedBase001033Phi
import NominalAlphaRepairedBase001034OpReflected001
import NominalAlphaRepairedBase001035Proj1Reflected001
import NominalAlphaRepairedBase001036Proj2Reflected001
import NominalAlphaRepairedBase001037OpabOpaqueHoisted004
import NominalAlphaRepairedBase001038Leaf1stReflected001
import NominalAlphaRepairedBase001039SwapReflected001
import NominalAlphaRepairedBase001040SsetReflected001
import NominalAlphaRepairedBase001041CoReflected001
import NominalAlphaRepairedBase001042ImaReflected001
import NominalAlphaRepairedBase001043SiReflected001
import NominalAlphaRepairedBase001044IdReflected001
import NominalAlphaRepairedBase001045XpReflected001
import NominalAlphaRepairedBase001046CnvReflected001
import NominalAlphaRepairedBase001047FvReflected001
import NominalAlphaRepairedBase001048Leaf2ndReflected001
import NominalAlphaRepairedBase001049OprabReflected001
import NominalAlphaPrefix050WppNotmem014Data
import NominalAlphaGlobal051ProofData001
import NominalAlphaRelease004Coarse052
import NominalAlphaRelease004Coarse053
import NominalAlphaRelease004Coarse054
import NominalAlphaRelease004Coarse055
import NominalAlphaRelease004Coarse056
import NominalAlphaRelease004Coarse057
import NominalAlphaRelease004Coarse058
import NominalAlphaRelease004Coarse059
import NominalAlphaRelease004Coarse060
import NominalAlphaRelease004Coarse061
import NominalAlphaRelease004Coarse062
import NominalAlphaRelease004Coarse063
import NominalAlphaRelease004Coarse064
import NominalAlphaRelease004Coarse065
import NominalAlphaRelease004Coarse066
import NominalAlphaRelease004Coarse067
import NominalAlphaRelease004Coarse068
import NominalAlphaRelease004Coarse069
import NominalAlphaRelease004Coarse070
import NominalAlphaRelease004Coarse071
import NominalAlphaRelease004Coarse072
import NominalAlphaRelease004Coarse073
import NominalAlphaRelease004Coarse074
import NominalAlphaRelease004Coarse075
import NominalAlphaRelease004Coarse076
import NominalAlphaRelease004Coarse077
import NominalAlphaRelease004Coarse078
import NominalAlphaRelease004Coarse079
import NominalAlphaRelease004Coarse080
import NominalAlphaRelease004Coarse081
import NominalAlphaRelease004Coarse082
import NominalAlphaRelease004Coarse083
import NominalAlphaRelease004Coarse084
import NominalAlphaRelease004Coarse085
import NominalAlphaRelease004Coarse086
import NominalAlphaRelease004Coarse087
import NominalAlphaHygieneV5Probe088
import NominalAlphaRelease004Coarse089
import NominalAlphaRelease004Coarse090
import NominalAlphaHygieneV5Coalesced091B
import NominalAlphaHygieneV5Coalesced092
import NominalAlphaHygieneV5Coalesced093
import NominalAlphaHygieneV5Coalesced094
import NominalAlphaHygieneV5Coalesced095
import NominalAlphaHygieneV5Coalesced096
import NominalAlphaHygieneV5Coalesced097
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk014Compact001Part027

set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

noncomputable def g_fdcolcodemapval
    (A : Class) (B : Class) (R : Class) (q : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_q : q ∉ A.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_q : q ∉ B.fv) (dv_R_q : q ∉ R.fv) (hyp_fdcolcodemapval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcolcodemapval_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcolcodemapval_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ ({q} : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_q : x ≠ q := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have dv_cache_0001 : x ∉ ((Class.cv q)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : Disjoint ((Class.cv q)).fv ((syn_cfdpointrel A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint ((Class.cv q)).fv ((syn_cfdpointrel A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel]; exact (show Disjoint (({q} : Finset Var)) ((A).fv) from (Finset.disjoint_singleton_left.mpr (show q ∉ (A).fv from (by exact dv_A_q))))))
  have dv_cache_0004 : Disjoint (A).fv (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0005 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0006 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : Disjoint ((syn_cpw1 (syn_cpw1 (.cv x)))).fv ((syn_cfdglobalrowmap R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint ((syn_cpw1 (syn_cpw1 (.cv x)))).fv ((syn_cfdglobalrowmap R A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdglobalrowmap]; exact (show Disjoint (((syn_cpw1 (.cv x))).fv) (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) from (Finset.disjoint_union_right.mpr ⟨(Finset.disjoint_union_right.mpr ⟨(show Disjoint (((syn_cpw1 (.cv x))).fv) ((A).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show Disjoint (((Class.cv x)).fv) ((A).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((A).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (A).fv from (by exact fresh_x_not_A)))))))), (show Disjoint (((syn_cpw1 (.cv x))).fv) ((B).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show Disjoint (((Class.cv x)).fv) ((B).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((B).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))⟩), (show Disjoint (((syn_cpw1 (.cv x))).fv) ((R).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show Disjoint (((Class.cv x)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))))⟩))))
  have dv_cache_0008 : Disjoint (A).fv ((syn_cuni (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (A).fv ((syn_cuni (syn_cuni (.cv q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((A).fv) (((syn_cuni (.cv q))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((A).fv) (((Class.cv q)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({q} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show q ∉ (A).fv from (by exact dv_A_q))))))))))
  have dv_cache_0009 : Disjoint (B).fv ((syn_cuni (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint (B).fv ((syn_cuni (syn_cuni (.cv q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((B).fv) (((syn_cuni (.cv q))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((B).fv) (((Class.cv q)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({q} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show q ∉ (B).fv from (by exact dv_B_q))))))))))
  have dv_cache_0010 : Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((syn_cuni (.cv q))).fv) ((R).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv q)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({q} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show q ∉ (R).fv from (by exact dv_R_q))))))))))
  have dv_cache_0011 : x ∉ ((Wff.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_q, fresh_x_not_A, fresh_x_not_B, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_A, fresh_x_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
  have p0001 :=
    @g_elpw12 x (.cv q) A dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_a1i (syn_wb (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (syn_wrex x A (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) p0001
  have p0003 :=
    @g_mpbid (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (syn_wrex x A (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) p0000 p0002
  have p0004 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
  have p0005 :=
    (by simpa [syn_cfdcolcodemap] using (Nominal.classEqRefl (syn_cfdcolcodemap R A B)))
  have p0006 :=
    @g_fveq1i (.cv q) (syn_cfdcolcodemap R A B) (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) p0005
  have p0007 :=
    @g_a1i (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (.cv q))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) p0006
  have p0008 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
  have p0009 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_cpw1 A)) (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A)))
  have p0010 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classEq (syn_cfv (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (.cv q)) (syn_cfv (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (.cv q))) p0008 p0009
  have p0011 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (.cv q)) (syn_cfv (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (.cv q)) p0007 p0010
  have p0012 :=
    @g_vex q
  have p0013 :=
    @g_fdpointrelex A hyp_fdcolcodemapval_2
  have p0014 :=
    @g_wppimagefn (syn_cfdpointrel A) p0013
  have p0015 :=
    @g_fvco2 (syn_cvv) (.cv q) (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))
  have p0016 :=
    @g_mpan (syn_wfn (syn_cimage (syn_cfdpointrel A)) (syn_cvv)) (.classMem (.cv q) (syn_cvv)) (.classEq (syn_cfv (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (.cv q)) (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q)))) p0014 p0015
  have p0017 :=
    Nominal.mp p0012 p0016
  have p0018 :=
    @g_a1i (.classEq (syn_cfv (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (.cv q)) (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q)))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) p0017
  have p0019 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (.cv q)) (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q))) p0011 p0018
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q)))) p0004 p0019
  have p0021 :=
    @g_fdpointrelex A hyp_fdcolcodemapval_2
  have p0022 :=
    @g_vex q
  have p0023 :=
    @g_wppfvimage (.cv q) (syn_cfdpointrel A) dv_cache_0003 p0021 p0022
  have p0024 :=
    @g_a1i (.classEq (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q)) (syn_cima (syn_cfdpointrel A) (.cv q))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) p0023
  have p0025 :=
    @g_simprr (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0026 :=
    @g_imaeq2d (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (.cv q) (syn_csn (syn_csn (.cv x))) (syn_cfdpointrel A) p0025
  have p0027 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q)) (syn_cima (syn_cfdpointrel A) (.cv q)) (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv x)))) p0024 p0026
  have p0028 :=
    @g_simprl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0029 :=
    @g_fdpointimage A x dv_cache_0002 hyp_fdcolcodemapval_2
  have p0030 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (.classMem (.cv x) A) (.classEq (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv x)))) (syn_cpw1 (syn_cpw1 (.cv x)))) p0028 p0029
  have p0031 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q)) (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv x)))) (syn_cpw1 (syn_cpw1 (.cv x))) p0027 p0030
  have p0032 :=
    @g_fveq2d (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q)) (syn_cpw1 (syn_cpw1 (.cv x))) (syn_cimage (syn_cfdglobalrowmap R A B)) p0031
  have p0033 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q))) (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cpw1 (syn_cpw1 (.cv x)))) p0020 p0032
  have p0034 :=
    @g_fdglobalrowex A B R dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_fdcolcodemapval_1 hyp_fdcolcodemapval_2 hyp_fdcolcodemapval_3
  have p0035 :=
    @g_vex x
  have p0036 :=
    @g_pw1ex (.cv x) p0035
  have p0037 :=
    @g_pw1ex (syn_cpw1 (.cv x)) p0036
  have p0038 :=
    @g_wppfvimage (syn_cpw1 (syn_cpw1 (.cv x))) (syn_cfdglobalrowmap R A B) dv_cache_0007 p0034 p0037
  have p0039 :=
    @g_a1i (.classEq (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cpw1 (syn_cpw1 (.cv x)))) (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (.cv x))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) p0038
  have p0040 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cpw1 (syn_cpw1 (.cv x)))) (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (.cv x)))) p0033 p0039
  have p0041 :=
    @g_simprr (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0042 :=
    @g_unieqd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (.cv q) (syn_csn (syn_csn (.cv x))) p0041
  have p0043 :=
    @g_snex (.cv x)
  have p0044 :=
    @g_unisn (syn_csn (.cv x)) p0043
  have p0045 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) p0044
  have p0046 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cuni (.cv q)) (syn_cuni (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv x)) p0042 p0045
  have p0047 :=
    @g_unieqd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cuni (.cv q)) (syn_csn (.cv x)) p0046
  have p0048 :=
    @g_vex x
  have p0049 :=
    @g_unisn (.cv x) p0048
  have p0050 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv x))) (.cv x)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) p0049
  have p0051 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_csn (.cv x))) (.cv x) p0047 p0050
  have p0052 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cuni (syn_cuni (.cv q))) (.cv x) p0051
  have p0053 :=
    @g_pw1eq (.cv x) (syn_cuni (syn_cuni (.cv q)))
  have p0054 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (.classEq (.cv x) (syn_cuni (syn_cuni (.cv q)))) (.classEq (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni (syn_cuni (.cv q))))) p0052 p0053
  have p0055 :=
    @g_pw1eq (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni (syn_cuni (.cv q))))
  have p0056 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (.classEq (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni (syn_cuni (.cv q))))) (.classEq (syn_cpw1 (syn_cpw1 (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cuni (syn_cuni (.cv q)))))) p0054 p0055
  have p0057 :=
    @g_imaeq2d (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cpw1 (syn_cpw1 (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cuni (syn_cuni (.cv q))))) (syn_cfdglobalrowmap R A B) p0056
  have p0058 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (.cv x)))) (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (syn_cuni (syn_cuni (.cv q)))))) p0040 p0057
  have p0059 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
  have p0060 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
  have p0061 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wbr R (syn_cwe) A) p0059 p0060
  have p0062 :=
    @g_simprl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0063 :=
    @g_simprr (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0064 :=
    @g_unieqd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (.cv q) (syn_csn (syn_csn (.cv x))) p0063
  have p0065 :=
    @g_snex (.cv x)
  have p0066 :=
    @g_unisn (syn_csn (.cv x)) p0065
  have p0067 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) p0066
  have p0068 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cuni (.cv q)) (syn_cuni (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv x)) p0064 p0067
  have p0069 :=
    @g_unieqd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cuni (.cv q)) (syn_csn (.cv x)) p0068
  have p0070 :=
    @g_vex x
  have p0071 :=
    @g_unisn (.cv x) p0070
  have p0072 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv x))) (.cv x)) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) p0071
  have p0073 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_csn (.cv x))) (.cv x) p0069 p0072
  have p0074 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cuni (syn_cuni (.cv q))) (.cv x) p0073
  have p0075 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (.cv x) (syn_cuni (syn_cuni (.cv q))) A p0074
  have p0076 :=
    @g_mpbid (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (.classMem (.cv x) A) (.classMem (syn_cuni (syn_cuni (.cv q))) A) p0062 p0075
  have p0077 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_wbr R (syn_cwe) A) (.classMem (syn_cuni (syn_cuni (.cv q))) A) p0061 p0076
  have p0078 :=
    @g_fdglobalrowima A B (syn_cuni (syn_cuni (.cv q))) R dv_cache_0004 dv_cache_0008 dv_cache_0005 dv_cache_0009 dv_cache_0006 dv_cache_0010
  have p0079 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (syn_cuni (syn_cuni (.cv q))) A)) (.classEq (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (syn_cuni (syn_cuni (.cv q)))))) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))) p0077 p0078
  have p0080 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))) (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (syn_cuni (syn_cuni (.cv q)))))) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))) p0058 p0079
  have p0081 :=
    @g_ex (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))) p0080
  have p0082 :=
    @g_exp3a (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))) p0081
  have p0083 :=
    @g_rexlimdv (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))) x A dv_cache_0011 dv_cache_0012 p0082
  have p0084 :=
    @g_mpd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wrex x A (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))) p0003 p0083
  exact p0084

noncomputable def g_fdcolcodemapf
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdcolcodemapf_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcolcodemapf_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcolcodemapf_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0004 : q ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : Disjoint (A).fv ((syn_cuni (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (A).fv ((syn_cuni (syn_cuni (.cv q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((A).fv) (((syn_cuni (.cv q))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((A).fv) (((Class.cv q)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({q} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show q ∉ (A).fv from (by exact fresh_q_not_A))))))))))
  have dv_cache_0008 : Disjoint (B).fv ((syn_cuni (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (B).fv ((syn_cuni (syn_cuni (.cv q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((B).fv) (((syn_cuni (.cv q))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint ((B).fv) (((Class.cv q)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({q} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show q ∉ (B).fv from (by exact fresh_q_not_B))))))))))
  have dv_cache_0009 : Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((syn_cuni (.cv q))).fv) ((R).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv q)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({q} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show q ∉ (R).fv from (by exact fresh_q_not_R))))))))))
  have dv_cache_0010 : q ∉ ((syn_wbr R (syn_cwe) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : q ∉ ((syn_cpw1 (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((syn_cpw (syn_cpw (syn_cfdif R A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((syn_cfdcolcodemap R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdcolcodemapfn A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapf_1 hyp_fdcolcodemapf_2 hyp_fdcolcodemapf_3
  have p0001 :=
    @g_fdcolcodemapfn A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapf_1 hyp_fdcolcodemapf_2 hyp_fdcolcodemapf_3
  have p0002 :=
    @g_fdcolcodemapval A B R q dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0003 dv_cache_0005 dv_cache_0006 hyp_fdcolcodemapf_1 hyp_fdcolcodemapf_2 hyp_fdcolcodemapf_3
  have p0003 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
  have p0004 :=
    @g_vex q
  have p0005 :=
    @g_uniex (.cv q) p0004
  have p0006 :=
    @g_uniex (syn_cuni (.cv q)) p0005
  have p0007 :=
    @g_fdcodeelpwpw2 A B (syn_cuni (syn_cuni (.cv q))) R dv_cache_0001 dv_cache_0007 dv_cache_0002 dv_cache_0008 dv_cache_0003 dv_cache_0009 hyp_fdcolcodemapf_1 hyp_fdcolcodemapf_2 hyp_fdcolcodemapf_3 p0006
  have p0008 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))) (syn_cpw (syn_cpw (syn_cfdif R A B)))) p0003 p0007
  have p0009 :=
    @g_eqeltrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))) (syn_cpw (syn_cpw (syn_cfdif R A B))) p0002 p0008
  have p0010 :=
    @g_ex (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (.classMem (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) p0009
  have p0011 :=
    @g_ralrimiv (syn_wbr R (syn_cwe) A) (.classMem (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) q (syn_cpw1 (syn_cpw1 A)) dv_cache_0010 p0010
  have p0012 :=
    @g_jca (syn_wbr R (syn_cwe) A) (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))) (syn_wral q (syn_cpw1 (syn_cpw1 A)) (.classMem (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cpw (syn_cpw (syn_cfdif R A B))))) p0001 p0011
  have p0013 :=
    @g_fnfvrnss q (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cfdcolcodemap R A B) dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0014 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wa (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))) (syn_wral q (syn_cpw1 (syn_cpw1 A)) (.classMem (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cpw (syn_cpw (syn_cfdif R A B)))))) (syn_wss (syn_crn (syn_cfdcolcodemap R A B)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) p0012 p0013
  have p0015 :=
    @g_jca (syn_wbr R (syn_cwe) A) (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))) (syn_wss (syn_crn (syn_cfdcolcodemap R A B)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) p0000 p0014
  have p0016 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))))
  have p0017 :=
    @g_sylibr (syn_wbr R (syn_cwe) A) (syn_wa (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))) (syn_wss (syn_crn (syn_cfdcolcodemap R A B)) (syn_cpw (syn_cpw (syn_cfdif R A B))))) (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) p0015 p0016
  exact p0017

noncomputable def g_fdcolcodearg
    (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) := by
  let proofSupport : Finset Var := A.fv ∪ ({q} : Finset Var)
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (h))
  have fresh_c_ne_q : c ≠ q := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_c : q ≠ c :=
    Ne.symm fresh_c_ne_q
  have dv_cache_0001 : c ∉ ((Class.cv q)).fv := by
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : c ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : c ∉ ((syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_q, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elpw12 c (.cv q) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (syn_wrex c A (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) p0000
  have p0002 :=
    @g_simpr (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))
  have p0003 :=
    @g_unieqd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (.cv q) (syn_csn (syn_csn (.cv c))) p0002
  have p0004 :=
    @g_snex (.cv c)
  have p0005 :=
    @g_unisn (syn_csn (.cv c)) p0004
  have p0006 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (syn_csn (.cv c)))) (syn_csn (.cv c))) (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) p0005
  have p0007 :=
    @g_eqtrd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_cuni (.cv q)) (syn_cuni (syn_csn (syn_csn (.cv c)))) (syn_csn (.cv c)) p0003 p0006
  have p0008 :=
    @g_unieqd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_cuni (.cv q)) (syn_csn (.cv c)) p0007
  have p0009 :=
    @g_vex c
  have p0010 :=
    @g_unisn (.cv c) p0009
  have p0011 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv c))) (.cv c)) (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) p0010
  have p0012 :=
    @g_eqtrd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_csn (.cv c))) (.cv c) p0008 p0011
  have p0013 :=
    @g_simpl (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))
  have p0014 :=
    @g_eqeltrd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_cuni (syn_cuni (.cv q))) (.cv c) A p0012 p0013
  have p0015 :=
    @g_simpr (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))
  have p0016 :=
    @g_simpr (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))
  have p0017 :=
    @g_unieqd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (.cv q) (syn_csn (syn_csn (.cv c))) p0016
  have p0018 :=
    @g_snex (.cv c)
  have p0019 :=
    @g_unisn (syn_csn (.cv c)) p0018
  have p0020 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (syn_csn (.cv c)))) (syn_csn (.cv c))) (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) p0019
  have p0021 :=
    @g_eqtrd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_cuni (.cv q)) (syn_cuni (syn_csn (syn_csn (.cv c)))) (syn_csn (.cv c)) p0017 p0020
  have p0022 :=
    @g_unieqd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_cuni (.cv q)) (syn_csn (.cv c)) p0021
  have p0023 :=
    @g_vex c
  have p0024 :=
    @g_unisn (.cv c) p0023
  have p0025 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv c))) (.cv c)) (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) p0024
  have p0026 :=
    @g_eqtrd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_csn (.cv c))) (.cv c) p0022 p0025
  have p0027 :=
    @g_sneqd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_cuni (syn_cuni (.cv q))) (.cv c) p0026
  have p0028 :=
    @g_sneqd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (.cv c)) p0027
  have p0029 :=
    @g_eqcomd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn (.cv c))) p0028
  have p0030 :=
    @g_eqtrd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (.cv q) (syn_csn (syn_csn (.cv c))) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) p0015 p0029
  have p0031 :=
    @g_jca (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0014 p0030
  have p0032 :=
    @g_rexlimiva (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) c A dv_cache_0003 p0031
  have p0033 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) (syn_wrex c A (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0001 p0032
  exact p0033

#print axioms g_fdcolcodearg

end NFChoice.DirectNominalPrf.WPPReplay
