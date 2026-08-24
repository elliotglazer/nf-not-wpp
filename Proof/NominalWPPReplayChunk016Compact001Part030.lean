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
import NominalWPPReplayChunk016Compact001Part029

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

noncomputable def g_wppcandstrictsliceleastdndvv
    (C : Class) (D : Class) (R : Class) (k : Var) (m : Var) (F : Class) (q : Var) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_C_q : q ∉ C.fv) (dv_D_k : k ∉ D.fv) (dv_D_m : m ∉ D.fv) (dv_D_q : q ∉ D.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_R_k : k ∉ R.fv) (dv_R_m : m ∉ R.fv) (dv_R_q : q ∉ R.fv) (dv_k_m : k ≠ m) (dv_k_q : k ≠ q) (dv_m_q : m ≠ q) (hyp_wppcandstrictsliceleastdndvv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wppcandstrictsliceleastdndvv_2 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_wppcandstrictsliceleastdndvv_3 : Nominal.NPrf (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))) :
    Nominal.NPrf (.imp (syn_wne (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ R.fv ∪ ({k} : Finset Var) ∪ ({m} : Finset Var) ∪ F.fv ∪ ({q} : Finset Var)
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_g_not_D : g ∉ D.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_g_not_R : g ∉ R.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_g_ne_k : g ≠ k := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_k_ne_g : k ≠ g :=
    Ne.symm fresh_g_ne_k
  have fresh_g_ne_m : g ≠ m := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_m_ne_g : m ≠ g :=
    Ne.symm fresh_g_ne_m
  have fresh_g_not_F : g ∉ F.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_ne_q : g ≠ q := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_g : q ≠ g :=
    Ne.symm fresh_g_ne_q
  have dv_cache_0001 : k ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : k ∉ ((syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_q, dv_F_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : g ∉ ((syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_C, fresh_g_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : k ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : g ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : k ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show k ≠ q from (by exact dv_k_q))
  have dv_cache_0011 : k ≠ g := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show k ≠ g from (by exact fresh_k_ne_g))
  have dv_cache_0012 : q ≠ g := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show q ≠ g from (by exact fresh_q_ne_g))
  have dv_cache_0013 : k ∉ ((Wff.classEq (.cv m) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_k_m, dv_D_k, dv_R_k, fresh_k_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : m ∉ ((syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_m, dv_R_m, fresh_m_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : m ∉ ((syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : m ∉ ((syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, dv_D_m, dv_R_m, fresh_m_ne_g, (Ne.symm dv_k_m), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : g ∉ ((syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_C, fresh_g_not_F, fresh_g_ne_m, fresh_g_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppcandstrictsliceexndv C F hyp_wppcandstrictsliceleastdndvv_2
  have p0001 :=
    @g_wecutcardrepleastdndv g D R k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) q dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_wppcandstrictsliceleastdndvv_1 p0000 hyp_wppcandstrictsliceleastdndvv_3
  have p0002 :=
    @g_id (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k))))
  have p0003 :=
    @g_id (.classEq (.cv m) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))))
  have p0004 :=
    @g_breq1d (.classEq (.cv m) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g)))))))) (.cv m) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (.cv k) (syn_clec) p0003
  have p0005 :=
    @g_ralbidv (.classEq (.cv m) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g)))))))) (syn_wbr (.cv m) (syn_clec) (.cv k)) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k)) k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) dv_cache_0013 p0004
  have p0006 :=
    @g_rspcev (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k))) m (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) dv_cache_0014 dv_cache_0015 dv_cache_0016 p0005
  have p0007 :=
    @g_syl (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k)))) (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k)))) (syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) p0002 p0006
  have p0008 :=
    @g_a1i (.imp (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k)))) (syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k))))) (.classMem (.cv g) (syn_cpw1 (syn_cpw1 D))) p0007
  have p0009 :=
    @g_rexlimiv (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k)))) (syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) g (syn_cpw1 (syn_cpw1 D)) dv_cache_0017 p0008
  have p0010 :=
    @g_syl (syn_wne (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (syn_wrex g (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv g))))))) (syn_clec) (.cv k))))) (syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) p0001 p0009
  exact p0010

noncomputable def g_wppcandstrictsliceleastextenddv
    (z : Var) (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_k_m : k ≠ m) (dv_k_z : k ≠ z) (dv_m_z : m ≠ z) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ C.fv ∪ ({k} : Finset Var) ∪ ({m} : Finset Var) ∪ F.fv
  have dv_cache_0001 : k ∉ ((Class.cv z)).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_k_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : k ∉ ((syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((syn_wbr (.cv m) (syn_clec) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_k_m, dv_k_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_z), dv_C_z, dv_F_z, (Ne.symm dv_k_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))
  have p0001 :=
    @g_elwppcandstrictslice C m F
  have p0002 :=
    @g_biimpi (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_cltc) C)) p0001
  have p0003 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_cltc) C)) p0000 p0002
  have p0004 :=
    @g_simpld (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv m) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_cltc) C) p0003
  have p0005 :=
    @g_simpr (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))
  have p0006 :=
    @g_elwppcandstrictslice C z F
  have p0007 :=
    @g_biimpri (.classMem (.cv z) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv z) (syn_cwppcand F C)) (syn_wbr (.cv z) (syn_cltc) C)) p0006
  have p0008 :=
    @g_ex (.classMem (.cv z) (syn_cwppcand F C)) (syn_wbr (.cv z) (syn_cltc) C) (.classMem (.cv z) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) p0007
  have p0009 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.classMem (.cv z) (syn_cwppcand F C)) (.imp (syn_wbr (.cv z) (syn_cltc) C) (.classMem (.cv z) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))) p0005 p0008
  have p0010 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))
  have p0011 :=
    @g_simpr (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))
  have p0012 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k))) p0010 p0011
  have p0013 :=
    @g_id (.classEq (.cv k) (.cv z))
  have p0014 :=
    @g_breq2d (.classEq (.cv k) (.cv z)) (.cv k) (.cv z) (.cv m) (syn_clec) p0013
  have p0015 :=
    @g_rspccv (syn_wbr (.cv m) (syn_clec) (.cv k)) (syn_wbr (.cv m) (syn_clec) (.cv z)) k (.cv z) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0014
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k))) (.imp (.classMem (.cv z) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wbr (.cv m) (syn_clec) (.cv z))) p0012 p0015
  have p0017 :=
    @g_syld (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (syn_wbr (.cv z) (syn_cltc) C) (.classMem (.cv z) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wbr (.cv m) (syn_clec) (.cv z)) p0009 p0016
  have p0018 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.neg (syn_wbr (.cv z) (syn_cltc) C))
  have p0019 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.neg (syn_wbr (.cv z) (syn_cltc) C))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) p0018 p0019
  have p0021 :=
    @g_simpl (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))
  have p0022 :=
    @g_elwppcandstrictslice C m F
  have p0023 :=
    @g_biimpi (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_cltc) C)) p0022
  have p0024 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_cltc) C)) p0021 p0023
  have p0025 :=
    @g_simprd (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv m) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_cltc) C) p0024
  have p0026 :=
    @g_brltc (.cv m) C
  have p0027 :=
    @g_biimpi (syn_wbr (.cv m) (syn_cltc) C) (syn_wa (syn_wbr (.cv m) (syn_clec) C) (syn_wne (.cv m) C)) p0026
  have p0028 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wbr (.cv m) (syn_cltc) C) (syn_wa (syn_wbr (.cv m) (syn_clec) C) (syn_wne (.cv m) C)) p0025 p0027
  have p0029 :=
    @g_simpld (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wbr (.cv m) (syn_clec) C) (syn_wne (.cv m) C) p0028
  have p0030 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.neg (syn_wbr (.cv z) (syn_cltc) C))) (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wbr (.cv m) (syn_clec) C) p0020 p0029
  have p0031 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.neg (syn_wbr (.cv z) (syn_cltc) C))
  have p0032 :=
    @g_simpr (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.neg (syn_wbr (.cv z) (syn_cltc) C))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.classMem (.cv z) (syn_cwppcand F C)) p0031 p0032
  have p0034 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.neg (syn_wbr (.cv z) (syn_cltc) C))
  have p0035 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.neg (syn_wbr (.cv z) (syn_cltc) C))) (.classMem (.cv z) (syn_cwppcand F C)) (.neg (syn_wbr (.cv z) (syn_cltc) C)) p0033 p0034
  have p0036 :=
    @g_wppcandnltpivoteqd C z F
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.neg (syn_wbr (.cv z) (syn_cltc) C))) (syn_wa (.classMem (.cv z) (syn_cwppcand F C)) (.neg (syn_wbr (.cv z) (syn_cltc) C))) (.classEq (.cv z) C) p0035 p0036
  have p0038 :=
    @g_breqtrrd (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.neg (syn_wbr (.cv z) (syn_cltc) C))) (.cv m) C (.cv z) (syn_clec) p0030 p0037
  have p0039 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (.neg (syn_wbr (.cv z) (syn_cltc) C)) (syn_wbr (.cv m) (syn_clec) (.cv z)) p0038
  have p0040 :=
    @g_pm2_61d (syn_wa (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C))) (syn_wbr (.cv z) (syn_cltc) C) (syn_wbr (.cv m) (syn_clec) (.cv z)) p0017 p0039
  have p0041 :=
    @g_ex (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv z) (syn_cwppcand F C)) (syn_wbr (.cv m) (syn_clec) (.cv z)) p0040
  have p0042 :=
    @g_ralrimiv (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wbr (.cv m) (syn_clec) (.cv z)) z (syn_cwppcand F C) dv_cache_0004 p0041
  have p0043 :=
    @g_jca (syn_wa (.classMem (.cv m) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (.cv m) (syn_cwppcand F C)) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))) p0004 p0042
  exact p0043

#print axioms g_wppcandstrictsliceleastextenddv

end NFChoice.DirectNominalPrf.WPPReplay
