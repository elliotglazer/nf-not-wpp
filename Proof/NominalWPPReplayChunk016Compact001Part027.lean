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
import NominalWPPReplayChunk016Compact001Part026

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

noncomputable def g_siwendv
    (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) D) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_siorndv D R
  have p0001 :=
    @g_sifrndv D R
  have p0002 :=
    @g_jca (syn_wbr R (syn_cwe) D) (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D)) p0000 p0001
  have p0003 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0004 :=
    @g_breqi (syn_csi R) (syn_cpw1 D) (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0003
  have p0005 :=
    @g_brin (syn_csi R) (syn_cpw1 D) (syn_cstrict) (syn_cfound)
  have p0006 :=
    @g_bitri (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cin (syn_cstrict) (syn_cfound)) (syn_cpw1 D)) (syn_wa (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D))) p0004 p0005
  have p0007 :=
    @g_biimpri (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D))) p0006
  have p0008 :=
    @g_syl (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D))) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) p0002 p0007
  exact p0008

noncomputable def g_wecutcardtypedleastndv
    (y : Var) (z : Var) (D : Class) (R : Class) (K : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_K_q : q ∉ K.fv) (dv_K_y : y ∉ K.fv) (dv_K_z : z ∉ K.fv) (dv_R_q : q ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_q_y : q ≠ y) (dv_q_z : q ≠ z) (dv_y_z : y ≠ z) (hyp_wecutcardtypedleastndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutcardtypedleastndv_2 : Nominal.NPrf (.classMem K (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)) (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ D.fv ∪ R.fv ∪ K.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ ((syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, dv_R_q, dv_K_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_csi (syn_csi R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_csi (syn_csi R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : q ∉ ((Wff.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_q_y, dv_D_q, dv_R_q, dv_K_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, dv_R_y, (Ne.symm dv_q_y), dv_K_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_z, dv_R_z, (Ne.symm dv_q_z), dv_K_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_q_y), dv_D_y, dv_R_y, dv_K_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Wff.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_q_z), dv_D_z, dv_R_z, dv_K_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : q ∉ ((Wff.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_q_z, dv_D_q, dv_R_q, dv_K_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : q ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show q ≠ y from (by exact dv_q_y))
  have dv_cache_0016 : q ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show q ≠ z from (by exact dv_q_z))
  have dv_cache_0017 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0018 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_abid2 q (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K) dv_cache_0001
  have p0001 :=
    @g_wecutcardfnex D R hyp_wecutcardtypedleastndv_1
  have p0002 :=
    @g_cnvex (syn_cwecutcardfn R D) p0001
  have p0003 :=
    @g_imaex (syn_ccnv (syn_cwecutcardfn R D)) K p0002 hyp_wecutcardtypedleastndv_2
  have p0004 :=
    @g_eqeltri (.cab q (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K) (syn_cvv) p0000 p0003
  have p0005 :=
    @g_eleq1 (.cv q) (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)
  have p0006 :=
    @g_eleq1 (.cv q) (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)
  have p0007 :=
    @g_siwendv D R
  have p0008 :=
    Nominal.mp hyp_wecutcardtypedleastndv_1 p0007
  have p0009 :=
    @g_siwendv (syn_cpw1 D) (syn_csi R)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_a1i (syn_wbr (syn_csi (syn_csi R)) (syn_cwe) (syn_cpw1 (syn_cpw1 D))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)) p0010
  have p0012 :=
    @g_id (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
  have p0013 :=
    @g_wecutcardpreimandv D R K q dv_cache_0002 dv_cache_0003
  have p0014 :=
    @g_biimprd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K) p0013
  have p0015 :=
    @g_reximia (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K) (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) q (syn_cpw1 (syn_cpw1 D)) p0014
  have p0016 :=
    @g_syl (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))) p0012 p0015
  have p0017_e01_recanon : Nominal.NPrf (.imp (.objEq q y) (syn_wb (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cwecutcardfn syn_cmpt syn_cpw1 syn_cin syn_cpw syn_wss syn_c1c syn_cnc syn_cec syn_cen
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0017_e02_recanon : Nominal.NPrf (.imp (.objEq q z) (syn_wb (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cwecutcardfn syn_cmpt syn_cpw1 syn_cin syn_cpw syn_wss syn_c1c syn_cnc syn_cec syn_cen
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0006
  have p0017 :=
    @g_weds (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)) (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) q y z (syn_cpw1 (syn_cpw1 D)) (syn_csi (syn_csi R)) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 p0004 p0017_e01_recanon p0017_e02_recanon p0011 p0016
  have p0018 :=
    @g_wecutcardpreimandv D R K y dv_cache_0018 dv_cache_0019
  have p0019 :=
    @g_wecutcardpreimandv D R K z dv_cache_0020 dv_cache_0021
  have p0020 :=
    @g_imbi1d (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) p0019
  have p0021 :=
    @g_ralbiia (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))) z (syn_cpw1 (syn_cpw1 D)) p0020
  have p0022 :=
    @g_a1i (syn_wb (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))) (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) p0021
  have p0023 :=
    @g_anbi12d (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))) p0018 p0022
  have p0024 :=
    @g_biimpd (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))) (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))) p0023
  have p0025 :=
    @g_reximia (syn_wa (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))) (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))) y (syn_cpw1 (syn_cpw1 D)) p0024
  have p0026 :=
    @g_syl (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)) (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))))) (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))))) p0017 p0025
  exact p0026

noncomputable def g_wecutssndv
    (x : Var) (y : Var) (D : Class) (R : Class) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) (hyp_wecutssndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_R, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0001 :=
    @g_id (.classEq (.cv x) (.cv y))
  have p0002 :=
    @g_sneqd (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) p0001
  have p0003 :=
    @g_imaeq2d (.classEq (.cv x) (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_ccnv (syn_cdif R (syn_cid))) p0002
  have p0004 :=
    @g_ineq2d (.classEq (.cv x) (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) D p0003
  have p0005 :=
    @g_eleq2d (.classEq (.cv x) (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv z) p0004
  have p0006 :=
    @g_biimpd (.classEq (.cv x) (.cv y)) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0005
  have p0007 :=
    @g_com12 (.classEq (.cv x) (.cv y)) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0006
  have p0008 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.imp (.classEq (.cv x) (.cv y)) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0000 p0007
  have p0009 :=
    @g_a1i (syn_wbr R (syn_cwe) D) (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) hyp_wecutssndv_1
  have p0010 :=
    @g_simpl (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))
  have p0011 :=
    @g_simpl (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) p0010 p0011
  have p0013 :=
    @g_simp2 (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv y) D) p0012 p0013
  have p0015 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D) p0009 p0014
  have p0016 :=
    @g_simpl (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))
  have p0017 :=
    @g_simpl (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) p0016 p0017
  have p0019 :=
    @g_simp1 (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv x) D) p0018 p0019
  have p0021 :=
    @g_simpl (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))
  have p0022 :=
    @g_simpl (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) p0021 p0022
  have p0024 :=
    @g_simp3 (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (syn_wbr (.cv x) R (.cv y)) p0023 p0024
  have p0026 :=
    @g_simpr (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))
  have p0027 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv x) (.cv y))))
  have p0028 :=
    @g_biimpri (syn_wne (.cv x) (.cv y)) (.neg (.classEq (.cv x) (.cv y))) p0027
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (.neg (.classEq (.cv x) (.cv y))) (syn_wne (.cv x) (.cv y)) p0026 p0028
  have p0030 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)) p0025 p0029
  have p0031 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))) p0020 p0030
  have p0032 :=
    @g_elstrictseg y x D R
  have p0033 :=
    @g_biimpri (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wa (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)))) p0032
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_wa (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)))) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0031 p0033
  have p0035 :=
    @g_simpl (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))
  have p0036 :=
    @g_simpr (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0035 p0036
  have p0038 :=
    @g_elstrictseg x z D R
  have p0039 :=
    @g_biimpi (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))) p0038
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))) p0037 p0039
  have p0041 :=
    @g_simpld (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))) p0040
  have p0042 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.classMem (.cv z) D) p0034 p0041
  have p0043 :=
    @g_simpl (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))
  have p0044 :=
    @g_simpr (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0043 p0044
  have p0046 :=
    @g_elstrictseg x z D R
  have p0047 :=
    @g_biimpi (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))) p0046
  have p0048 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))) p0045 p0047
  have p0049 :=
    @g_simprd (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))) p0048
  have p0050 :=
    @g_simpld (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)) p0049
  have p0051 :=
    @g_n_3jca (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wa (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv x)) p0015 p0042 p0050
  have p0052 :=
    @g_strictsegdown y x z D R
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y)))) (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wa (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv x))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0051 p0052
  have p0054 :=
    @g_ex (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (.cv x) (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0053
  have p0055 :=
    @g_pm2_61d (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classEq (.cv x) (.cv y)) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0008 p0054
  have p0056 :=
    @g_ex (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv z) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0055
  have p0057 :=
    @g_ssrdv (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) z (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0056
  exact p0057

noncomputable def g_wecutnclecndv
    (x : Var) (y : Var) (D : Class) (R : Class) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) (hyp_wecutnclecndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv
  have dv_cache_0001 : x ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_wecutssndv x y D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 hyp_wecutnclecndv_1
  have p0001 :=
    @g_brex R D (syn_cwe)
  have p0002 :=
    Nominal.mp hyp_wecutnclecndv_1 p0001
  have p0003 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0004 :=
    @g_brex R D (syn_cwe)
  have p0005 :=
    Nominal.mp hyp_wecutnclecndv_1 p0004
  have p0006 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0005
  have p0007 :=
    @g_idex
  have p0008 :=
    @g_difex R (syn_cid) p0006 p0007
  have p0009 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0008
  have p0010 :=
    @g_snex (.cv x)
  have p0011 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0009 p0010
  have p0012 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0003 p0011
  have p0013 :=
    @g_brex R D (syn_cwe)
  have p0014 :=
    Nominal.mp hyp_wecutnclecndv_1 p0013
  have p0015 :=
    @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0014
  have p0016 :=
    @g_brex R D (syn_cwe)
  have p0017 :=
    Nominal.mp hyp_wecutnclecndv_1 p0016
  have p0018 :=
    @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0017
  have p0019 :=
    @g_idex
  have p0020 :=
    @g_difex R (syn_cid) p0018 p0019
  have p0021 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0020
  have p0022 :=
    @g_snex (.cv y)
  have p0023 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)) p0021 p0022
  have p0024 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) p0015 p0023
  have p0025 :=
    @g_nclec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) p0012 p0024
  have p0026 :=
    @g_syl (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0000 p0025
  exact p0026

#print axioms g_wecutnclecndv

end NFChoice.DirectNominalPrf.WPPReplay
