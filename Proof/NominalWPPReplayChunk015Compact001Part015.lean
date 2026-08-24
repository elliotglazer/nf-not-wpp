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
import NominalWPPReplayChunk015Compact001Part014

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

noncomputable def g_finleastadjndv
    (k : Var) (m : Var) (n : Var) (X : Class) (Y : Class) (dv_X_k : k ∉ X.fv) (dv_X_m : m ∉ X.fv) (dv_X_n : n ∉ X.fv) (dv_Y_k : k ∉ Y.fv) (dv_Y_m : m ∉ Y.fv) (dv_Y_n : n ∉ Y.fv) (dv_k_m : k ≠ m) (dv_k_n : k ≠ n) (dv_m_n : m ≠ n) :
    Nominal.NPrf (.imp (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))) := by
  let proofSupport : Finset Var := ({k} : Finset Var) ∪ ({m} : Finset Var) ∪ ({n} : Finset Var) ∪ X.fv ∪ Y.fv
  have dv_cache_0001 : n ∉ ((Class.cv k)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((Wff.imp (.classMem (.cv k) Y) (.classMem (syn_cplc (.cv k) (syn_c1c)) X))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_n), dv_Y_n, dv_X_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((syn_cplc (.cv k) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.imp (.classMem (syn_cplc (.cv k) (syn_c1c)) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_n), dv_X_n, (Ne.symm dv_m_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Wff.imp (.classMem (.cv m) X) (.classMem (.cv m) Y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_n), dv_X_n, dv_Y_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((Wff.imp (.classMem (.cv m) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_n), dv_Y_n, (Ne.symm dv_k_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simp2 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0001 :=
    @g_simpr (.classMem (.cv m) X) (.classMem (.cv k) Y)
  have p0002 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (.classMem (.cv k) Y) p0000 p0001
  have p0003 :=
    @g_simp3 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0004 :=
    @g_simpr (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))
  have p0005 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))) p0003 p0004
  have p0006 :=
    @g_simpr (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))
  have p0007 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))) p0005 p0006
  have p0008 :=
    @g_simp1 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0009 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
  have p0010 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc)) p0008 p0009
  have p0011 :=
    @g_jca (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))) (.classMem (.cv k) (syn_cnnc)) p0007 p0010
  have p0012 :=
    @g_eleq1 (.cv n) (.cv k) Y
  have p0013 :=
    @g_addceq1 (.cv n) (.cv k) (syn_c1c)
  have p0014 :=
    @g_eleq1d (.classEq (.cv n) (.cv k)) (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv k) (syn_c1c)) X p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv n) (.cv k)) (.classMem (.cv n) Y) (.classMem (.cv k) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X) (.classMem (syn_cplc (.cv k) (syn_c1c)) X) p0012 p0014
  have p0016 :=
    @g_rspccva (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)) (.imp (.classMem (.cv k) Y) (.classMem (syn_cplc (.cv k) (syn_c1c)) X)) n (.cv k) (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0015
  have p0017 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))) (.classMem (.cv k) (syn_cnnc))) (.imp (.classMem (.cv k) Y) (.classMem (syn_cplc (.cv k) (syn_c1c)) X)) p0011 p0016
  have p0018 :=
    @g_mpd (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (.classMem (.cv k) Y) (.classMem (syn_cplc (.cv k) (syn_c1c)) X) p0002 p0017
  have p0019 :=
    @g_simp3 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0020 :=
    @g_simpl (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))
  have p0021 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) p0019 p0020
  have p0022 :=
    @g_simpl (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))
  have p0023 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) p0021 p0022
  have p0024 :=
    @g_simp1 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0025 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
  have p0026 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc)) p0024 p0025
  have p0027 :=
    @g_peano2 (.cv k)
  have p0028 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (.classMem (.cv k) (syn_cnnc)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc)) p0026 p0027
  have p0029 :=
    @g_jca (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc)) p0023 p0028
  have p0030 :=
    @g_eleq1 (.cv n) (syn_cplc (.cv k) (syn_c1c)) X
  have p0031 :=
    @g_breq2 (.cv n) (syn_cplc (.cv k) (syn_c1c)) (.cv m) (syn_ckqrel (syn_clefin))
  have p0032 :=
    @g_imbi12d (.classEq (.cv n) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv n) X) (.classMem (syn_cplc (.cv k) (syn_c1c)) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))) p0030 p0031
  have p0033 :=
    @g_rspccva (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (syn_cplc (.cv k) (syn_c1c)) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c)))) n (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc) dv_cache_0004 dv_cache_0002 dv_cache_0005 p0032
  have p0034 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc))) (.imp (.classMem (syn_cplc (.cv k) (syn_c1c)) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c)))) p0029 p0033
  have p0035 :=
    @g_mpd (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (.classMem (syn_cplc (.cv k) (syn_c1c)) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))) p0018 p0034
  have p0036 :=
    @g_simp1 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0037 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
  have p0038 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc)) p0036 p0037
  have p0039 :=
    @g_simp1 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0040 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
  have p0041 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv m) (syn_cnnc)) p0039 p0040
  have p0042 :=
    @g_jca (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)) p0038 p0041
  have p0043 :=
    @g_kqfinsucsplit (.cv k) (.cv m)
  have p0044 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))) (syn_wb (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))) (syn_wo (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))) p0042 p0043
  have p0045 :=
    @g_biimpd (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))) (syn_wo (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) p0044
  have p0046 :=
    @g_mpd (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))) (syn_wo (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) p0035 p0045
  have p0047 :=
    @g_simpr (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0048 :=
    @g_simpl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0049 :=
    @g_simp2 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0050 :=
    @g_simpl (.classMem (.cv m) X) (.classMem (.cv k) Y)
  have p0051 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (.classMem (.cv m) X) p0049 p0050
  have p0052 :=
    @g_simp3 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0053 :=
    @g_simpr (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))
  have p0054 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))) p0052 p0053
  have p0055 :=
    @g_simpl (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))
  have p0056 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) p0054 p0055
  have p0057 :=
    @g_simp1 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0058 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
  have p0059 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv m) (syn_cnnc)) p0057 p0058
  have p0060 :=
    @g_jca (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (.classMem (.cv m) (syn_cnnc)) p0056 p0059
  have p0061 :=
    @g_eleq1 (.cv n) (.cv m) X
  have p0062 :=
    @g_eleq1 (.cv n) (.cv m) Y
  have p0063 :=
    @g_imbi12d (.classEq (.cv n) (.cv m)) (.classMem (.cv n) X) (.classMem (.cv m) X) (.classMem (.cv n) Y) (.classMem (.cv m) Y) p0061 p0062
  have p0064 :=
    @g_rspccva (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)) (.imp (.classMem (.cv m) X) (.classMem (.cv m) Y)) n (.cv m) (syn_cnnc) dv_cache_0006 dv_cache_0002 dv_cache_0007 p0063
  have p0065 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (.classMem (.cv m) (syn_cnnc))) (.imp (.classMem (.cv m) X) (.classMem (.cv m) Y)) p0060 p0064
  have p0066 :=
    @g_mpd (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (.classMem (.cv m) X) (.classMem (.cv m) Y) p0051 p0065
  have p0067 :=
    @g_simp3 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0068 :=
    @g_simpl (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))
  have p0069 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) p0067 p0068
  have p0070 :=
    @g_simpr (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))
  have p0071 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0069 p0070
  have p0072 :=
    @g_simp1 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0073 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
  have p0074 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv m) (syn_cnnc)) p0072 p0073
  have p0075 :=
    @g_jca (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (.classMem (.cv m) (syn_cnnc)) p0071 p0074
  have p0076 :=
    @g_eleq1 (.cv n) (.cv m) Y
  have p0077 :=
    @g_breq2 (.cv n) (.cv m) (.cv k) (syn_ckqrel (syn_clefin))
  have p0078 :=
    @g_imbi12d (.classEq (.cv n) (.cv m)) (.classMem (.cv n) Y) (.classMem (.cv m) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)) p0076 p0077
  have p0079 :=
    @g_rspccva (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (.cv m) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m))) n (.cv m) (syn_cnnc) dv_cache_0006 dv_cache_0002 dv_cache_0008 p0078
  have p0080 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (.classMem (.cv m) (syn_cnnc))) (.imp (.classMem (.cv m) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m))) p0075 p0079
  have p0081 :=
    @g_mpd (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (.classMem (.cv m) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)) p0066 p0080
  have p0082 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)) p0048 p0081
  have p0083 :=
    @g_jca (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)) p0047 p0082
  have p0084 :=
    @g_simpl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0085 :=
    @g_simp1 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0086 :=
    @g_kqfinantinn (.cv m) (.cv k)
  have p0087 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.imp (syn_wa (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m))) (.classEq (.cv m) (.cv k))) p0085 p0086
  have p0088 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (.imp (syn_wa (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m))) (.classEq (.cv m) (.cv k))) p0084 p0087
  have p0089 :=
    @g_mpd (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m))) (.classEq (.cv m) (.cv k)) p0083 p0088
  have p0090 :=
    @g_orc (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
  have p0091 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (.cv m) (.cv k)) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) p0089 p0090
  have p0092 :=
    @g_ex (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) p0091
  have p0093 :=
    @g_id (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
  have p0094 :=
    @g_olc (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (.classEq (.cv m) (.cv k))
  have p0095 :=
    @g_syl (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) p0093 p0094
  have p0096 :=
    @g_a1i (.imp (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) p0095
  have p0097 :=
    @g_jaod (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) p0092 p0096
  have p0098 :=
    @g_mpd (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))) (syn_wo (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) p0046 p0097
  exact p0098

#print axioms g_finleastadjndv

end NFChoice.DirectNominalPrf.WPPReplay
