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
import NominalWPPReplayChunk016Compact001Part042

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

noncomputable def g_wppcandleastreundv
    (ph : Wff) (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_k_m : k ≠ m) (dv_k_ph : k ∉ ph.fv) (dv_m_ph : m ∉ ph.fv) (hyp_wppcandleastreundv_1 : Nominal.NPrf (.imp ph (syn_wrex m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))) :
    Nominal.NPrf (.imp ph (syn_wreu m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))) := by
  let proofSupport : Finset Var := ph.fv ∪ C.fv ∪ ({k} : Finset Var) ∪ ({m} : Finset Var) ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_ph : n ∉ ph.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_ne_k : n ≠ k := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_k_ne_n : k ≠ n :=
    Ne.symm fresh_n_ne_k
  have fresh_n_ne_m : n ≠ m := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ ((Class.cv n)).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : k ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((syn_wbr (.cv m) (syn_clec) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_k_m, fresh_k_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : k ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_k_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : k ∉ ((syn_wbr (.cv n) (syn_clec) (.cv m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_n, dv_k_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : m ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : m ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show m ≠ n from (by exact fresh_m_ne_n))
  have dv_cache_0010 : k ∉ ((Wff.classEq (.cv m) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_k_m, fresh_k_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : m ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : n ∉ ((syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F, fresh_n_ne_m, fresh_n_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : m ∉ ((syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, fresh_m_ne_n, (Ne.symm dv_k_m), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_tru
  have p0001 :=
    @g_simpr (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
  have p0002 :=
    @g_simpl (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))
  have p0003 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) p0001 p0002
  have p0004 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
  have p0005 :=
    @g_simpr (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))
  have p0006 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (.classMem (.cv n) (syn_cwppcand F C)) p0004 p0005
  have p0007 :=
    @g_id (.classEq (.cv k) (.cv n))
  have p0008 :=
    @g_breq2d (.classEq (.cv k) (.cv n)) (.cv k) (.cv n) (.cv m) (syn_clec) p0007
  have p0009 :=
    @g_rspcv (syn_wbr (.cv m) (syn_clec) (.cv k)) (syn_wbr (.cv m) (syn_clec) (.cv n)) k (.cv n) (syn_cwppcand F C) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (.classMem (.cv n) (syn_cwppcand F C)) (.imp (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wbr (.cv m) (syn_clec) (.cv n))) p0006 p0009
  have p0011 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wbr (.cv m) (syn_clec) (.cv n)) p0003 p0010
  have p0012 :=
    @g_simpr (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
  have p0013 :=
    @g_simpr (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))
  have p0014 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))) p0012 p0013
  have p0015 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
  have p0016 :=
    @g_simpl (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (.classMem (.cv m) (syn_cwppcand F C)) p0015 p0016
  have p0018 :=
    @g_id (.classEq (.cv k) (.cv m))
  have p0019 :=
    @g_breq2d (.classEq (.cv k) (.cv m)) (.cv k) (.cv m) (.cv n) (syn_clec) p0018
  have p0020 :=
    @g_rspcv (syn_wbr (.cv n) (syn_clec) (.cv k)) (syn_wbr (.cv n) (syn_clec) (.cv m)) k (.cv m) (syn_cwppcand F C) dv_cache_0004 dv_cache_0002 dv_cache_0005 p0019
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (.classMem (.cv m) (syn_cwppcand F C)) (.imp (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))) (syn_wbr (.cv n) (syn_clec) (.cv m))) p0017 p0020
  have p0022 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))) (syn_wbr (.cv n) (syn_clec) (.cv m)) p0014 p0021
  have p0023 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wbr (.cv m) (syn_clec) (.cv n)) (syn_wbr (.cv n) (syn_clec) (.cv m)) p0011 p0022
  have p0024 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
  have p0025 :=
    @g_simpl (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (.classMem (.cv m) (syn_cwppcand F C)) p0024 p0025
  have p0027 :=
    @g_elwppcand C (.cv m) F
  have p0028 :=
    @g_biimpi (.classMem (.cv m) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C)) (.classMem (.cv m) (syn_cwppreach F C))) p0027
  have p0029 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (.classMem (.cv m) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C)) (.classMem (.cv m) (syn_cwppreach F C))) p0026 p0028
  have p0030 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C)) (.classMem (.cv m) (syn_cwppreach F C))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C)) (.classMem (.cv m) (syn_cwppreach F C))) (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C)) p0029 p0030
  have p0032 :=
    @g_simpl (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C)
  have p0033 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C)) (.classMem (.cv m) (syn_chwcards (syn_cvv))) p0031 p0032
  have p0034 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
  have p0035 :=
    @g_simpr (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))
  have p0036 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (.classMem (.cv n) (syn_cwppcand F C)) p0034 p0035
  have p0037 :=
    @g_elwppcand C (.cv n) F
  have p0038 :=
    @g_biimpi (.classMem (.cv n) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C)) (.classMem (.cv n) (syn_cwppreach F C))) p0037
  have p0039 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (.classMem (.cv n) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C)) (.classMem (.cv n) (syn_cwppreach F C))) p0036 p0038
  have p0040 :=
    @g_simpl (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C)) (.classMem (.cv n) (syn_cwppreach F C))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C)) (.classMem (.cv n) (syn_cwppreach F C))) (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C)) p0039 p0040
  have p0042 :=
    @g_simpl (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C)
  have p0043 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C)) (.classMem (.cv n) (syn_chwcards (syn_cvv))) p0041 p0042
  have p0044 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (.classMem (.cv m) (syn_chwcards (syn_cvv))) (.classMem (.cv n) (syn_chwcards (syn_cvv))) p0033 p0043
  have p0045 :=
    @g_hwcardslecanti m n
  have p0046 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv))) (.classMem (.cv n) (syn_chwcards (syn_cvv)))) (.imp (syn_wa (syn_wbr (.cv m) (syn_clec) (.cv n)) (syn_wbr (.cv n) (syn_clec) (.cv m))) (.classEq (.cv m) (.cv n))) p0044 p0045
  have p0047 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) (syn_wa (syn_wbr (.cv m) (syn_clec) (.cv n)) (syn_wbr (.cv n) (syn_clec) (.cv m))) (.classEq (.cv m) (.cv n)) p0023 p0046
  have p0048 :=
    @g_ex (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))) (.classEq (.cv m) (.cv n)) p0047
  have p0049 :=
    @g_a1i (.imp (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))) (.imp (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))) (.classEq (.cv m) (.cv n)))) syn_wtru p0048
  have p0050 :=
    @g_ralrimivv syn_wtru (.imp (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))) (.classEq (.cv m) (.cv n))) m n (syn_cwppcand F C) (syn_cwppcand F C) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0049
  have p0051 :=
    Nominal.mp p0000 p0050
  have p0052 :=
    @g_a1i (syn_wral m (syn_cwppcand F C) (syn_wral n (syn_cwppcand F C) (.imp (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))) (.classEq (.cv m) (.cv n))))) ph p0051
  have p0053 :=
    @g_jca ph (syn_wrex m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wral m (syn_cwppcand F C) (syn_wral n (syn_cwppcand F C) (.imp (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))) (.classEq (.cv m) (.cv n))))) hyp_wppcandleastreundv_1 p0052
  have p0054 :=
    @g_id (.classEq (.cv m) (.cv n))
  have p0055 :=
    @g_breq1d (.classEq (.cv m) (.cv n)) (.cv m) (.cv n) (.cv k) (syn_clec) p0054
  have p0056 :=
    @g_ralbidv (.classEq (.cv m) (.cv n)) (syn_wbr (.cv m) (syn_clec) (.cv k)) (syn_wbr (.cv n) (syn_clec) (.cv k)) k (syn_cwppcand F C) dv_cache_0010 p0055
  have p0057_e00_recanon : Nominal.NPrf (.imp (.objEq m n) (syn_wb (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wral syn_cwppcand syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cwppreach syn_cuni syn_wex syn_crn syn_cima syn_wrex syn_wbr syn_cop syn_cun syn_cvv syn_cfrec syn_cclos1 syn_cint syn_csn syn_cpprod syn_ctxp syn_ccom syn_copab syn_c1st syn_cmpt syn_cplc syn_c1c syn_cimage syn_ccnv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0056
  have p0057 :=
    @g_reu4 (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))) m n (syn_cwppcand F C) dv_cache_0011 dv_cache_0006 dv_cache_0012 dv_cache_0013 dv_cache_0009 p0057_e00_recanon
  have p0058_e00_recanon : Nominal.NPrf (syn_wb (syn_wreu m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wa (syn_wrex m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wral m (syn_cwppcand F C) (syn_wral n (syn_cwppcand F C) (.imp (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))) (.classEq (.cv m) (.cv n))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wreu syn_weu syn_wex syn_wa syn_cwppcand syn_cin syn_ccompl syn_cnin syn_wnan syn_cwppreach syn_cuni syn_crn syn_cima syn_wrex syn_wbr syn_cop syn_cun syn_cvv syn_cfrec syn_cclos1 syn_cint syn_csn syn_cpprod syn_ctxp syn_ccom syn_copab syn_c1st syn_cmpt syn_cplc syn_c1c syn_cimage syn_ccnv syn_wral
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wreu, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0057
  have p0058 :=
    @g_biimpri (syn_wreu m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wa (syn_wrex m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wral m (syn_cwppcand F C) (syn_wral n (syn_cwppcand F C) (.imp (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))) (.classEq (.cv m) (.cv n)))))) p0058_e00_recanon
  have p0059 :=
    @g_syl ph (syn_wa (syn_wrex m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wral m (syn_cwppcand F C) (syn_wral n (syn_cwppcand F C) (.imp (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))) (.classEq (.cv m) (.cv n)))))) (syn_wreu m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))) p0053 p0058
  exact p0059

noncomputable def g_wppgammaminpackndv
    (ph : Wff) (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_k_m : k ≠ m) (dv_k_ph : k ∉ ph.fv) (dv_m_ph : m ∉ ph.fv) (hyp_wppgammaminpackndv_1 : Nominal.NPrf (.imp ph (syn_wrex m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))) :
    Nominal.NPrf (.imp ph (syn_wa (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k))))) := by
  let proofSupport : Finset Var := ph.fv ∪ C.fv ∪ ({k} : Finset Var) ∪ ({m} : Finset Var) ∪ F.fv
  have dv_cache_0001 : k ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : m ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : m ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : k ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show k ≠ m from (by exact dv_k_m))
  have dv_cache_0006 : k ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_k_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : m ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_m_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : k ∉ ((Wff.classEq (.cv m) (syn_cwppgamma F C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_k_m, dv_C_k, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : m ∉ ((syn_cwppgamma F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : m ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : m ∉ ((syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, (Ne.symm dv_k_m), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wppgamma C k m F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_a1i (.classEq (syn_cwppgamma F C) (syn_cio m (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))) ph p0000
  have p0002 :=
    @g_wppcandleastreundv ph C k m F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_wppgammaminpackndv_1
  have p0003 :=
    @g_reiotacl2 (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) m (syn_cwppcand F C)
  have p0004 :=
    @g_syl ph (syn_wreu m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (.classMem (syn_cio m (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))) (syn_crab m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))) p0002 p0003
  have p0005 :=
    @g_eqeltrd ph (syn_cwppgamma F C) (syn_cio m (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))) (syn_crab m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))) p0001 p0004
  have p0006 :=
    @g_id (.classEq (.cv m) (syn_cwppgamma F C))
  have p0007 :=
    @g_breq1d (.classEq (.cv m) (syn_cwppgamma F C)) (.cv m) (syn_cwppgamma F C) (.cv k) (syn_clec) p0006
  have p0008 :=
    @g_ralbidv (.classEq (.cv m) (syn_cwppgamma F C)) (syn_wbr (.cv m) (syn_clec) (.cv k)) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k)) k (syn_cwppcand F C) dv_cache_0008 p0007
  have p0009 :=
    @g_elrab (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k))) m (syn_cwppgamma F C) (syn_cwppcand F C) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0008
  have p0010 :=
    @g_biimpi (.classMem (syn_cwppgamma F C) (syn_crab m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))) (syn_wa (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k)))) p0009
  have p0011 :=
    @g_syl ph (.classMem (syn_cwppgamma F C) (syn_crab m (syn_cwppcand F C) (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))) (syn_wa (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k)))) p0005 p0010
  exact p0011

noncomputable def g_wppgammaminhwndv
    (C : Class) (k : Var) (F : Class) (dv_C_k : k ∉ C.fv) (dv_F_k : k ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wa (.classMem (syn_cwppgamma F C) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k))))) := by
  let proofSupport : Finset Var := C.fv ∪ ({k} : Finset Var) ∪ F.fv
  let m : Var := freshVar proofSupport 0
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_ne_k : m ≠ k := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_m : k ≠ m :=
    Ne.symm fresh_m_ne_k
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have dv_cache_0001 : m ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : k ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : m ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : k ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : m ≠ k := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show m ≠ k from (by exact fresh_m_ne_k))
  have dv_cache_0006 : k ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show k ≠ m from (by exact fresh_k_ne_m))
  have dv_cache_0007 : k ∉ ((syn_wa (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_k, dv_C_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ ((syn_wa (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_F, fresh_m_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppcandminhwndv k C m F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_wppgammaminpackndv (syn_wa (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv)))) C k m F dv_cache_0002 dv_cache_0001 dv_cache_0004 dv_cache_0003 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0000
  exact p0001

noncomputable def g_wppcardtfnexndv
     :
    Nominal.NPrf (.classMem (syn_cwppcardtfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_tcfnex
  have p0001 :=
    @g_ncsex
  have p0002 :=
    @g_pw1ex (syn_cncs) p0001
  have p0003 :=
    @g_resex (syn_ctcfn) (syn_cpw1 (syn_cncs)) p0000 p0002
  have p0004 :=
    (by simpa [syn_cwppcardtfn] using (Nominal.classEqRefl (syn_cwppcardtfn)))
  have p0005 :=
    @g_eleq1i (syn_cwppcardtfn) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_cvv) p0004
  have p0006 :=
    @g_mpbir (.classMem (syn_cwppcardtfn) (syn_cvv)) (.classMem (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_cvv)) p0003 p0005
  exact p0006

noncomputable def g_wppcardtfnvalndv
    (q : Var) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_ctc (syn_cuni (.cv q))))) := by
  let proofSupport : Finset Var := ({q} : Finset Var)
  have p0000 :=
    (by simpa [syn_cwppcardtfn] using (Nominal.classEqRefl (syn_cwppcardtfn)))
  have p0001 :=
    @g_fveq1i (.cv q) (syn_cwppcardtfn) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) p0000
  have p0002 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (.cv q))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) p0001
  have p0003 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_cncs)) (syn_ctcfn)
  have p0004 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (.cv q)) (syn_cfv (syn_ctcfn) (.cv q)) p0002 p0003
  have p0005 :=
    @g_hnwpw1argcl (syn_cncs) q
  have p0006 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0005
  have p0007 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_ctcfn) p0006
  have p0008 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) p0004 p0007
  have p0009 :=
    @g_hnwpw1argcl (syn_cncs) q
  have p0010 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0009
  have p0011 :=
    @g_elex (syn_cuni (.cv q)) (syn_cncs)
  have p0012 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_tcfnfvcl (syn_cuni (.cv q))
  have p0014 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))) p0012 p0013
  have p0015 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))) p0008 p0014
  exact p0015

noncomputable def g_wppcardtfnmapndv
     :
    Nominal.NPrf (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have dv_cache_0001 : q ∉ ((syn_cpw1 (syn_cncs))).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cwppcardtfn)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardtfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fntcfn
  have p0001 :=
    @g_pw1ss1c (syn_cncs)
  have p0002 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (syn_wss (syn_cpw1 (syn_cncs)) (syn_c1c)) p0000 p0001
  have p0003 :=
    @g_fnssres (syn_c1c) (syn_cpw1 (syn_cncs)) (syn_ctcfn)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    (by simpa [syn_cwppcardtfn] using (Nominal.classEqRefl (syn_cwppcardtfn)))
  have p0006 :=
    @g_fneq1i (syn_cpw1 (syn_cncs)) (syn_cwppcardtfn) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) p0005
  have p0007 :=
    @g_mpbir (syn_wfn (syn_cwppcardtfn) (syn_cpw1 (syn_cncs))) (syn_wfn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs))) p0004 p0006
  have p0008 :=
    (by simpa [syn_cwppcardtfn] using (Nominal.classEqRefl (syn_cwppcardtfn)))
  have p0009 :=
    @g_fveq1i (.cv q) (syn_cwppcardtfn) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) p0008
  have p0010 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (.cv q))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) p0009
  have p0011 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_cncs)) (syn_ctcfn)
  have p0012 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (.cv q)) (syn_cfv (syn_ctcfn) (.cv q)) p0010 p0011
  have p0013 :=
    @g_hnwpw1argcl (syn_cncs) q
  have p0014 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0013
  have p0015 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_ctcfn) p0014
  have p0016 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) p0012 p0015
  have p0017 :=
    @g_hnwpw1argcl (syn_cncs) q
  have p0018 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0017
  have p0019 :=
    @g_elex (syn_cuni (.cv q)) (syn_cncs)
  have p0020 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_tcfnfvcl (syn_cuni (.cv q))
  have p0022 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))) p0020 p0021
  have p0023 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))) p0016 p0022
  have p0024 :=
    @g_hnwpw1argcl (syn_cncs) q
  have p0025 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0024
  have p0026 :=
    @g_tccl (syn_cuni (.cv q))
  have p0027 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classMem (syn_ctc (syn_cuni (.cv q))) (syn_cncs)) p0025 p0026
  have p0028 :=
    @g_eqeltrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_ctc (syn_cuni (.cv q))) (syn_cncs) p0023 p0027
  have p0029 :=
    @g_rgen (.classMem (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cncs)) q (syn_cpw1 (syn_cncs)) p0028
  have p0030 :=
    @g_pm3_2i (syn_wfn (syn_cwppcardtfn) (syn_cpw1 (syn_cncs))) (syn_wral q (syn_cpw1 (syn_cncs)) (.classMem (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cncs))) p0007 p0029
  have p0031 :=
    @g_ffnfv q (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0032 :=
    @g_mpbir (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) (syn_wa (syn_wfn (syn_cwppcardtfn) (syn_cpw1 (syn_cncs))) (syn_wral q (syn_cpw1 (syn_cncs)) (.classMem (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cncs)))) p0030 p0031
  exact p0032

#print axioms g_wppcardtfnmapndv

end NFChoice.DirectNominalPrf.WPPReplay
