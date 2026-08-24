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
import NominalWPPReplayChunk016Compact001Part044

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

noncomputable def g_wppnnstageextcbidv
    (D : Class) (H : Class) (p : Var) (a : Var) (dv_D_a : a ∉ D.fv) (dv_D_p : p ∉ D.fv) (dv_H_a : a ∉ H.fv) (dv_H_p : p ∉ H.fv) (dv_a_p : a ≠ p) :
    Nominal.NPrf (syn_wb (syn_wrex a (syn_cnnc) (.classMem D (syn_cfv H (.cv a)))) (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p)))))) := by
  let proofSupport : Finset Var := D.fv ∪ H.fv ∪ ({p} : Finset Var) ∪ ({a} : Finset Var)
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_n_not_H : n ∉ H.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_ne_p : n ≠ p := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_n : p ≠ n :=
    Ne.symm fresh_n_ne_p
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_n : a ≠ n :=
    Ne.symm fresh_n_ne_a
  have dv_cache_0001 : n ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((Wff.classMem D (syn_cfv H (syn_ctc (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_p, fresh_p_ne_n, dv_H_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_D, fresh_n_ne_p, fresh_n_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_a, fresh_n_not_D, fresh_n_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_a, dv_a_p, dv_H_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ ((syn_ctc (.cv p))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_a_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((Wff.classMem D (syn_cfv H (syn_ctc (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_a, dv_a_p, dv_H_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((syn_wrex a (syn_cnnc) (.classMem D (syn_cfv H (.cv a))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_p, (Ne.symm dv_a_p), dv_H_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))
  have p0001 :=
    @g_nntcpreim n (.cv a) dv_cache_0001
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classMem (.cv a) (syn_cnnc)) (syn_wrex n (syn_cnnc) (.classEq (syn_ctc (.cv n)) (.cv a))) p0000 p0001
  have p0003 :=
    @g_simp2 (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))
  have p0004 :=
    @g_simp1 (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))
  have p0005 :=
    @g_simpr (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))
  have p0006 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))) (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classMem D (syn_cfv H (.cv a))) p0004 p0005
  have p0007 :=
    @g_simp3 (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))
  have p0008 :=
    @g_id (.classEq (syn_ctc (.cv n)) (.cv a))
  have p0009 :=
    @g_fveq2d (.classEq (syn_ctc (.cv n)) (.cv a)) (syn_ctc (.cv n)) (.cv a) H p0008
  have p0010 :=
    @g_eleq2d (.classEq (syn_ctc (.cv n)) (.cv a)) (syn_cfv H (syn_ctc (.cv n))) (syn_cfv H (.cv a)) D p0009
  have p0011 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))) (.classEq (syn_ctc (.cv n)) (.cv a)) (syn_wb (.classMem D (syn_cfv H (syn_ctc (.cv n)))) (.classMem D (syn_cfv H (.cv a)))) p0007 p0010
  have p0012 :=
    @g_mpbird (syn_w3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))) (.classMem D (syn_cfv H (syn_ctc (.cv n)))) (.classMem D (syn_cfv H (.cv a))) p0006 p0011
  have p0013 :=
    @g_jca (syn_w3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))) (.classMem (.cv n) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv n)))) p0003 p0012
  have p0014 :=
    @g_tceq (.cv p) (.cv n)
  have p0015 :=
    @g_fveq2d (.classEq (.cv p) (.cv n)) (syn_ctc (.cv p)) (syn_ctc (.cv n)) H p0014
  have p0016 :=
    @g_eleq2d (.classEq (.cv p) (.cv n)) (syn_cfv H (syn_ctc (.cv p))) (syn_cfv H (syn_ctc (.cv n))) D p0015
  have p0017 :=
    @g_rspcev (.classMem D (syn_cfv H (syn_ctc (.cv p)))) (.classMem D (syn_cfv H (syn_ctc (.cv n)))) p (.cv n) (syn_cnnc) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0016
  have p0018 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv n))))) (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) p0013 p0017
  have p0019 :=
    @g_rexlimdv3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (.classEq (syn_ctc (.cv n)) (.cv a)) (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) n (syn_cnnc) dv_cache_0005 dv_cache_0006 p0018
  have p0020 :=
    @g_mpd (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))) (syn_wrex n (syn_cnnc) (.classEq (syn_ctc (.cv n)) (.cv a))) (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) p0002 p0019
  have p0021 :=
    @g_rexlimiva (.classMem D (syn_cfv H (.cv a))) (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) a (syn_cnnc) dv_cache_0007 p0020
  have p0022 :=
    @g_simpl (.classMem (.cv p) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p))))
  have p0023 :=
    @g_nntccl (.cv p)
  have p0024 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) (.classMem (.cv p) (syn_cnnc)) (.classMem (syn_ctc (.cv p)) (syn_cnnc)) p0022 p0023
  have p0025 :=
    @g_simpr (.classMem (.cv p) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p))))
  have p0026 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) (.classMem (syn_ctc (.cv p)) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p)))) p0024 p0025
  have p0027 :=
    @g_id (.classEq (.cv a) (syn_ctc (.cv p)))
  have p0028 :=
    @g_fveq2d (.classEq (.cv a) (syn_ctc (.cv p))) (.cv a) (syn_ctc (.cv p)) H p0027
  have p0029 :=
    @g_eleq2d (.classEq (.cv a) (syn_ctc (.cv p))) (syn_cfv H (.cv a)) (syn_cfv H (syn_ctc (.cv p))) D p0028
  have p0030 :=
    @g_rspcev (.classMem D (syn_cfv H (.cv a))) (.classMem D (syn_cfv H (syn_ctc (.cv p)))) a (syn_ctc (.cv p)) (syn_cnnc) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0029
  have p0031 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) (syn_wa (.classMem (syn_ctc (.cv p)) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) (syn_wrex a (syn_cnnc) (.classMem D (syn_cfv H (.cv a)))) p0026 p0030
  have p0032 :=
    @g_rexlimiva (.classMem D (syn_cfv H (syn_ctc (.cv p)))) (syn_wrex a (syn_cnnc) (.classMem D (syn_cfv H (.cv a)))) p (syn_cnnc) dv_cache_0011 p0031
  have p0033 :=
    @g_impbii (syn_wrex a (syn_cnnc) (.classMem D (syn_cfv H (.cv a)))) (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) p0021 p0032
  exact p0033

noncomputable def g_wppreachtcrexvndv
    (C : Class) (D : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_F_n : n ∉ F.fv) (hyp_wppreachtcrexvndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem D (syn_cwppreach F C)) (syn_wrex n (syn_cnnc) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ ({n} : Finset Var) ∪ F.fv
  let m : Var := freshVar proofSupport 0
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_m_not_D : m ∉ D.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_m : n ≠ m :=
    Ne.symm fresh_m_ne_n
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have dv_cache_0001 : m ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : m ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : m ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ ((syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_F, fresh_m_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : m ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show m ≠ n from (by exact fresh_m_ne_n))
  have p0000 :=
    @g_elwppreachvndv C D m F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wppreachtcrexvndv_1
  have p0001 :=
    @g_wppnnstageextcbidv D (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) n m dv_cache_0002 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0002 :=
    @g_bitri (.classMem D (syn_cwppreach F C)) (syn_wrex m (syn_cnnc) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (.cv m)))) (syn_wrex n (syn_cnnc) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n))))) p0000 p0001
  exact p0002

noncomputable def g_wppreachlayerorbvndv
    (C : Class) (D : Class) (F : Class) (N : Class) (hyp_wppreachlayerorbvndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppreachlayerorbvndv_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wppreachlayerorbvndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppreachlayerorbvndv_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N)))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ F.fv ∪ N.fv
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_N : c ∉ N.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv c)).fv (F).fv := by
    exact (show Disjoint ((Class.cv c)).fv (F).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({c} : Finset Var)) ((F).fv) from (Finset.disjoint_singleton_left.mpr (show c ∉ (F).fv from (by exact fresh_c_not_F))))))
  have dv_cache_0002 : c ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : c ∉ ((Wff.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_N, fresh_c_not_D, fresh_c_not_F, fresh_c_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqidd (.classEq (.cv c) C) (syn_cimage (syn_ccnv F))
  have p0001 :=
    @g_id (.classEq (.cv c) C)
  have p0002 :=
    @g_sneqd (.classEq (.cv c) C) (.cv c) C p0001
  have p0003 :=
    @g_imaeq2d (.classEq (.cv c) C) (syn_csn (.cv c)) (syn_csn C) (syn_clec) p0002
  have p0004 :=
    @g_jca (.classEq (.cv c) C) (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F))) (.classEq (syn_cima (syn_clec) (syn_csn (.cv c))) (syn_cima (syn_clec) (syn_csn C))) p0000 p0003
  have p0005 :=
    @g_freceq12 (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c))) (syn_cima (syn_clec) (syn_csn C))
  have p0006 :=
    @g_syl (.classEq (.cv c) C) (syn_wa (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F))) (.classEq (syn_cima (syn_clec) (syn_csn (.cv c))) (syn_cima (syn_clec) (syn_csn C)))) (.classEq (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c)))) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) p0004 p0005
  have p0007 :=
    @g_fveq1d (.classEq (.cv c) C) (syn_ctc N) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c)))) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0006
  have p0008 :=
    @g_eleq2d (.classEq (.cv c) C) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c)))) (syn_ctc N)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N)) D p0007
  have p0009 :=
    @g_id (.classEq (.cv c) C)
  have p0010 :=
    @g_breq1d (.classEq (.cv c) C) (.cv c) C (syn_cfv (syn_cfrec F D) N) (syn_clec) p0009
  have p0011 :=
    @g_bibi12d (.classEq (.cv c) C) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c)))) (syn_ctc N))) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (syn_wbr (.cv c) (syn_clec) (syn_cfv (syn_cfrec F D) N)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N)) p0008 p0010
  have p0012 :=
    @g_imbi2d (.classEq (.cv c) C) (syn_wb (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c)))) (syn_ctc N))) (syn_wbr (.cv c) (syn_clec) (syn_cfv (syn_cfrec F D) N))) (syn_wb (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N))) (.classMem N (syn_cnnc)) p0011
  have p0013 :=
    @g_wppreachlayerorbfin (.cv c) D F N dv_cache_0001 hyp_wppreachlayerorbvndv_1 hyp_wppreachlayerorbvndv_2 hyp_wppreachlayerorbvndv_3
  have p0014 :=
    @g_vtoclg (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c)))) (syn_ctc N))) (syn_wbr (.cv c) (syn_clec) (syn_cfv (syn_cfrec F D) N)))) (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N)))) c C (syn_cvv) dv_cache_0002 dv_cache_0003 p0012 p0013
  have p0015 :=
    Nominal.mp hyp_wppreachlayerorbvndv_4 p0014
  exact p0015

noncomputable def g_wppreachlayerorbrexvndv
    (C : Class) (D : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_F_n : n ∉ F.fv) (hyp_wppreachlayerorbrexvndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppreachlayerorbrexvndv_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wppreachlayerorbrexvndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppreachlayerorbrexvndv_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wrex n (syn_cnnc) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n))))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ ({n} : Finset Var) ∪ F.fv
  have p0000 :=
    @g_wppreachlayerorbvndv C D F (.cv n) hyp_wppreachlayerorbrexvndv_1 hyp_wppreachlayerorbrexvndv_2 hyp_wppreachlayerorbrexvndv_3 hyp_wppreachlayerorbrexvndv_4
  have p0001 :=
    @g_rexbiia (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) n (syn_cnnc) p0000
  exact p0001

noncomputable def g_wppreachfwdrexvndv
    (C : Class) (D : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_F_n : n ∉ F.fv) (hyp_wppreachfwdrexvndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppreachfwdrexvndv_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wppreachfwdrexvndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppreachfwdrexvndv_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem D (syn_cwppreach F C)) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ ({n} : Finset Var) ∪ F.fv
  have dv_cache_0001 : n ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex F (syn_cfuns)
  have p0001 :=
    Nominal.mp hyp_wppreachfwdrexvndv_1 p0000
  have p0002 :=
    @g_wppreachtcrexvndv C D n F dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @g_wppreachlayerorbrexvndv C D n F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wppreachfwdrexvndv_1 hyp_wppreachfwdrexvndv_2 hyp_wppreachfwdrexvndv_3 hyp_wppreachfwdrexvndv_4
  have p0004 :=
    @g_bitri (.classMem D (syn_cwppreach F C)) (syn_wrex n (syn_cnnc) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n))))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) p0002 p0003
  exact p0004

noncomputable def g_wppreachtcbidv
    (x : Var) (C : Class) (D : Class) (F : Class) (G : Class) (r : Var) (dv_D_r : r ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) (hyp_wppreachtcbidv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppreachtcbidv_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wppreachtcbidv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppreachtcbidv_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppreachtcbidv_5 : Nominal.NPrf (.classMem (syn_ctc D) (syn_cdm G))) (hyp_wppreachtcbidv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wppreachtcbidv_7 : Nominal.NPrf (syn_wral x (syn_cdm F) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x)))))) (hyp_wppreachtcbidv_8 : Nominal.NPrf (.classMem C (syn_cncs))) (hyp_wppreachtcbidv_9 : Nominal.NPrf (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs)))) :
    Nominal.NPrf (syn_wb (.classMem D (syn_cwppreach F C)) (.classMem (syn_ctc D) (syn_cwppreach G (syn_ctc C)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ C.fv ∪ D.fv ∪ F.fv ∪ G.fv ∪ ({r} : Finset Var)
  let p : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_F : p ∉ F.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_G : p ∉ G.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_p : r ≠ p :=
    Ne.symm fresh_p_ne_r
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_r : a ≠ r := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_a : r ≠ a :=
    Ne.symm fresh_a_ne_r
  have fresh_p_ne_a : p ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_p : a ≠ p :=
    Ne.symm fresh_p_ne_a
  have dv_cache_0001 : a ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : r ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show a ≠ p from (by exact fresh_a_ne_p))
  have dv_cache_0015 : a ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0016 : p ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((syn_ctc D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex C (syn_cncs)
  have p0001 :=
    Nominal.mp hyp_wppreachtcbidv_8 p0000
  have p0002 :=
    @g_wppreachfwdrexvndv C D a F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wppreachtcbidv_1 hyp_wppreachtcbidv_2 hyp_wppreachtcbidv_3 p0001
  have p0003 :=
    @g_wppreachorbitextcbidv x C D F G r p a dv_cache_0001 dv_cache_0004 dv_cache_0002 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 hyp_wppreachtcbidv_1 hyp_wppreachtcbidv_2 hyp_wppreachtcbidv_3 hyp_wppreachtcbidv_4 hyp_wppreachtcbidv_5 hyp_wppreachtcbidv_6 hyp_wppreachtcbidv_7 hyp_wppreachtcbidv_8 hyp_wppreachtcbidv_9
  have p0004 :=
    @g_bitri (.classMem D (syn_cwppreach F C)) (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) (syn_wrex p (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) p0002 p0003
  have p0005 :=
    @g_tccl C
  have p0006 :=
    Nominal.mp hyp_wppreachtcbidv_8 p0005
  have p0007 :=
    @g_elex (syn_ctc C) (syn_cncs)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_wppreachfwdrexvndv (syn_ctc C) (syn_ctc D) p G dv_cache_0016 dv_cache_0017 dv_cache_0012 hyp_wppreachtcbidv_4 hyp_wppreachtcbidv_5 hyp_wppreachtcbidv_6 p0008
  have p0010 :=
    @g_bitr4i (.classMem D (syn_cwppreach F C)) (syn_wrex p (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (syn_ctc D) (syn_cwppreach G (syn_ctc C))) p0004 p0009
  exact p0010

noncomputable def g_elhwcardsweclndv
    (K : Class) (s : Var) (d : Var) (dv_K_d : d ∉ K.fv) (dv_K_s : s ∉ K.fv) (dv_d_s : d ≠ s) :
    Nominal.NPrf (.imp (.classMem K (syn_cvv)) (syn_wb (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))))) := by
  let proofSupport : Finset Var := K.fv ∪ ({s} : Finset Var) ∪ ({d} : Finset Var)
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_K : k ∉ K.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_ne_s : k ≠ s := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_s_ne_k : s ≠ k :=
    Ne.symm fresh_k_ne_s
  have fresh_k_ne_d : k ≠ d := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_k : d ≠ k :=
    Ne.symm fresh_k_ne_d
  have dv_cache_0001 : s ∉ ((Wff.classEq (.cv k) K)).fv := by
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_k, dv_K_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : d ∉ ((Wff.classEq (.cv k) K)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_k, dv_K_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ≠ k := by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ k from (by exact fresh_d_ne_k))
  have dv_cache_0004 : d ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show d ≠ s from (by exact dv_d_s))
  have dv_cache_0005 : k ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show k ≠ s from (by exact fresh_k_ne_s))
  have dv_cache_0006 : k ∉ (K).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : k ∉ ((syn_wb (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_K, fresh_k_ne_s, fresh_k_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv k) K)
  have p0001 :=
    @g_eleq1d (.classEq (.cv k) K) (.cv k) K (syn_chwcards (syn_cvv)) p0000
  have p0002 :=
    @g_id (.classEq (.cv k) K)
  have p0003 :=
    @g_eqeq1d (.classEq (.cv k) K) (.cv k) K (syn_cnc (.cv d)) p0002
  have p0004 :=
    @g_anbi2d (.classEq (.cv k) K) (.classEq (.cv k) (syn_cnc (.cv d))) (.classEq K (syn_cnc (.cv d))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) p0003
  have p0005 :=
    @g_exbidv (.classEq (.cv k) K) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) s dv_cache_0001 p0004
  have p0006 :=
    @g_exbidv (.classEq (.cv k) K) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) d dv_cache_0002 p0005
  have p0007 :=
    @g_bibi12d (.classEq (.cv k) K) (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))) p0001 p0006
  have p0008 :=
    @g_elhwcardswev k s d dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 :=
    @g_vtoclg (syn_wb (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))))) (syn_wb (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))))) k K (syn_cvv) dv_cache_0006 dv_cache_0007 p0007 p0008
  exact p0009

#print axioms g_elhwcardsweclndv

end NFChoice.DirectNominalPrf.WPPReplay
