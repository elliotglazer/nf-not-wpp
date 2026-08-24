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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk010Compact001Part001

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

noncomputable def g_evenoddnnnul
     :
    Nominal.NPrf (.classEq (syn_cun (syn_cevenfin) (syn_coddfin)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_ne_n : x ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_x : n ≠ x :=
    Ne.symm fresh_x_ne_n
  have fresh_x_ne_m : x ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    Ne.symm fresh_x_ne_m
  have fresh_x_ne_k : x ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_k_ne_x : k ≠ x :=
    Ne.symm fresh_x_ne_k
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_n_ne_k : n ≠ k := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_n : k ≠ n :=
    Ne.symm fresh_n_ne_k
  have fresh_m_ne_k : m ≠ k := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_m : k ≠ m :=
    Ne.symm fresh_m_ne_k
  have dv_cache_0001 : x ∉ ((syn_cevenfin)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cdif (syn_cnnc) (syn_csn (syn_c0)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_coddfin)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : m ∉ ((syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : m ∉ ((Wff.imp (syn_wne (.cv k) (syn_c0)) (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : k ∉ ((Wff.imp (syn_wne (.cv m) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ ((Wff.imp (syn_wne (syn_c0c) (syn_c0)) (.classMem (syn_c0c) (syn_cun (syn_cevenfin) (syn_coddfin))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : m ∉ ((Wff.imp (syn_wne (.cv n) (syn_c0)) (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : m ∉ ((Wff.imp (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : m ≠ k := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show m ≠ k from (by exact fresh_m_ne_k))
  have dv_cache_0012 : n ∉ ((syn_cdif (syn_cnnc) (syn_csn (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((syn_cun (syn_cevenfin) (syn_coddfin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_evennn (.cv x)
  have p0001 :=
    @g_evennnul (.cv x)
  have p0002 :=
    @g_eldifsn (.cv x) (syn_cnnc) (syn_c0)
  have p0003 :=
    @g_sylanbrc (.classMem (.cv x) (syn_cevenfin)) (.classMem (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)) (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0000 p0001 p0002
  have p0004 :=
    @g_ssriv x (syn_cevenfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) dv_cache_0001 dv_cache_0002 p0003
  have p0005 :=
    @g_oddnn (.cv x)
  have p0006 :=
    @g_oddnnul (.cv x)
  have p0007 :=
    @g_sylanbrc (.classMem (.cv x) (syn_coddfin)) (.classMem (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)) (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0005 p0006 p0002
  have p0008 :=
    @g_ssriv x (syn_coddfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) dv_cache_0003 dv_cache_0002 p0007
  have p0009 :=
    @g_pm3_2i (syn_wss (syn_cevenfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (syn_wss (syn_coddfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0004 p0008
  have p0010 :=
    @g_unss (syn_cevenfin) (syn_coddfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))
  have p0011 :=
    @g_mpbi (syn_wa (syn_wss (syn_cevenfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (syn_wss (syn_coddfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))) (syn_wss (syn_cun (syn_cevenfin) (syn_coddfin)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0009 p0010
  have p0012 :=
    @g_eldifsn (.cv n) (syn_cnnc) (syn_c0)
  have p0013 :=
    @g_vex m
  have p0014 :=
    @g_elsnc (.cv m) (syn_c0) p0013
  have p0015 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv m) (syn_c0))))
  have p0016 :=
    @g_con2bii (syn_wne (.cv m) (syn_c0)) (.classEq (.cv m) (syn_c0)) p0015
  have p0017 :=
    @g_bitri (.classMem (.cv m) (syn_csn (syn_c0))) (.classEq (.cv m) (syn_c0)) (.neg (syn_wne (.cv m) (syn_c0))) p0014 p0016
  have p0018 :=
    @g_orbi1i (.classMem (.cv m) (syn_csn (syn_c0))) (.neg (syn_wne (.cv m) (syn_c0))) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))) p0017
  have p0019 :=
    @g_elun (.cv m) (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin))
  have p0020 :=
    @g_imor (syn_wne (.cv m) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))
  have p0021 :=
    @g_n_3bitr4i (syn_wo (.classMem (.cv m) (syn_csn (syn_c0))) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))) (syn_wo (.neg (syn_wne (.cv m) (syn_c0))) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))) (.classMem (.cv m) (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin)))) (.imp (syn_wne (.cv m) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))) p0018 p0019 p0020
  have p0022 :=
    @g_eqabi (.imp (syn_wne (.cv m) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))) m (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin))) dv_cache_0004 p0021
  have p0023 :=
    @g_snex (syn_c0)
  have p0024 :=
    @g_evenfinex
  have p0025 :=
    @g_oddfinex
  have p0026 :=
    @g_unex (syn_cevenfin) (syn_coddfin) p0024 p0025
  have p0027 :=
    @g_unex (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin)) p0023 p0026
  have p0028 :=
    @g_eqeltrri (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin))) (.cab m (.imp (syn_wne (.cv m) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))))) (syn_cvv) p0022 p0027
  have p0029 :=
    @g_neeq1 (.cv m) (syn_c0c) (syn_c0)
  have p0030 :=
    @g_eleq1 (.cv m) (syn_c0c) (syn_cun (syn_cevenfin) (syn_coddfin))
  have p0031 :=
    @g_imbi12d (.classEq (.cv m) (syn_c0c)) (syn_wne (.cv m) (syn_c0)) (syn_wne (syn_c0c) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))) (.classMem (syn_c0c) (syn_cun (syn_cevenfin) (syn_coddfin))) p0029 p0030
  have p0032 :=
    @g_neeq1 (.cv m) (.cv k) (syn_c0)
  have p0033 :=
    @g_eleq1 (.cv m) (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))
  have p0034_e00_recanon : Nominal.NPrf (.imp (.objEq m k) (syn_wb (syn_wne (.cv m) (syn_c0)) (syn_wne (.cv k) (syn_c0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0032
  have p0034_e01_recanon : Nominal.NPrf (.imp (.objEq m k) (syn_wb (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))) (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cevenfin syn_coddfin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0033
  have p0034 :=
    @g_imbi12d (.objEq m k) (syn_wne (.cv m) (syn_c0)) (syn_wne (.cv k) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))) (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))) p0034_e00_recanon p0034_e01_recanon
  have p0035 :=
    @g_neeq1 (.cv m) (syn_cplc (.cv k) (syn_c1c)) (syn_c0)
  have p0036 :=
    @g_eleq1 (.cv m) (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin))
  have p0037 :=
    @g_imbi12d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_wne (.cv m) (syn_c0)) (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin))) p0035 p0036
  have p0038 :=
    @g_neeq1 (.cv m) (.cv n) (syn_c0)
  have p0039 :=
    @g_eleq1 (.cv m) (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))
  have p0040_e00_recanon : Nominal.NPrf (.imp (.objEq m n) (syn_wb (syn_wne (.cv m) (syn_c0)) (syn_wne (.cv n) (syn_c0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0038
  have p0040_e01_recanon : Nominal.NPrf (.imp (.objEq m n) (syn_wb (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))) (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cevenfin syn_coddfin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0039
  have p0040 :=
    @g_imbi12d (.objEq m n) (syn_wne (.cv m) (syn_c0)) (syn_wne (.cv n) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))) (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))) p0040_e00_recanon p0040_e01_recanon
  have p0041 :=
    @g_ssun1 (syn_cevenfin) (syn_coddfin)
  have p0042 :=
    @g_n_0ceven
  have p0043 :=
    @g_sselii (syn_cevenfin) (syn_cun (syn_cevenfin) (syn_coddfin)) (syn_c0c) p0041 p0042
  have p0044 :=
    @g_a1i (.classMem (syn_c0c) (syn_cun (syn_cevenfin) (syn_coddfin))) (syn_wne (syn_c0c) (syn_c0)) p0043
  have p0045 :=
    @g_addcnnul (.cv k) (syn_c1c)
  have p0046 :=
    @g_simpld (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (syn_wne (.cv k) (syn_c0)) (syn_wne (syn_c1c) (syn_c0)) p0045
  have p0047 :=
    @g_sucevenodd (.cv k)
  have p0048 :=
    @g_expcom (.classMem (.cv k) (syn_cevenfin)) (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin)) p0047
  have p0049 :=
    @g_sucoddeven (.cv k)
  have p0050 :=
    @g_expcom (.classMem (.cv k) (syn_coddfin)) (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin)) p0049
  have p0051 :=
    @g_orim12d (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (.classMem (.cv k) (syn_cevenfin)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin)) (.classMem (.cv k) (syn_coddfin)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin)) p0048 p0050
  have p0052 :=
    @g_elun (.cv k) (syn_cevenfin) (syn_coddfin)
  have p0053 :=
    @g_elun (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin) (syn_coddfin)
  have p0054 :=
    @g_orcom (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin))
  have p0055 :=
    @g_bitri (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin))) (syn_wo (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin))) (syn_wo (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin))) p0053 p0054
  have p0056 :=
    @g_n_3imtr4g (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (syn_wo (.classMem (.cv k) (syn_cevenfin)) (.classMem (.cv k) (syn_coddfin))) (syn_wo (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin))) (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin))) p0051 p0052 p0055
  have p0057 :=
    @g_embantd (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (syn_wne (.cv k) (syn_c0)) (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin))) p0046 p0056
  have p0058 :=
    @g_com12 (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (.imp (syn_wne (.cv k) (syn_c0)) (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin)))) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin))) p0057
  have p0059 :=
    @g_a1i (.imp (.imp (syn_wne (.cv k) (syn_c0)) (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin)))) (.imp (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin))))) (.classMem (.cv k) (syn_cnnc)) p0058
  have p0060_e04_recanon : Nominal.NPrf (.imp (.classEq (.cv m) (.cv n)) (syn_wb (.imp (syn_wne (.cv m) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))) (.imp (syn_wne (.cv n) (syn_c0)) (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv syn_cun syn_cevenfin syn_coddfin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0040
  have p0060 :=
    @g_finds (.imp (syn_wne (.cv m) (syn_c0)) (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))) (.imp (syn_wne (syn_c0c) (syn_c0)) (.classMem (syn_c0c) (syn_cun (syn_cevenfin) (syn_coddfin)))) (.imp (syn_wne (.cv k) (syn_c0)) (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin)))) (.imp (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin)))) (.imp (syn_wne (.cv n) (syn_c0)) (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin)))) m k (.cv n) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0028 p0031 p0034 p0037 p0060_e04_recanon p0044 p0059
  have p0061 :=
    @g_imp (.classMem (.cv n) (syn_cnnc)) (syn_wne (.cv n) (syn_c0)) (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))) p0060
  have p0062 :=
    @g_sylbi (.classMem (.cv n) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (.cv n) (syn_c0))) (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))) p0012 p0061
  have p0063 :=
    @g_ssriv n (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cun (syn_cevenfin) (syn_coddfin)) dv_cache_0012 dv_cache_0013 p0062
  have p0064 :=
    @g_eqssi (syn_cun (syn_cevenfin) (syn_coddfin)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) p0011 p0063
  exact p0064

#print axioms g_evenoddnnnul

end NFChoice.DirectNominalPrf.WPPReplay
