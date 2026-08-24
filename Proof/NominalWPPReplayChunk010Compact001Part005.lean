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
import NominalWPPReplayChunk010Compact001Part004

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

noncomputable def g_eventfin
    (M : Class) :
    Nominal.NPrf (.imp (.classMem M (syn_cevenfin)) (.classMem (syn_ctfin M) (syn_cevenfin))) := by
  let proofSupport : Finset Var := M.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (h)
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (h)
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_x_ne_m : x ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    Ne.symm fresh_x_ne_m
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) M)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (.cv n) (.cv n)))) (syn_wne M (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : m ∉ ((syn_ctfin (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : m ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ ((Wff.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : m ∉ ((Wff.classEq (.cv x) (syn_ctfin (syn_cplc (.cv n) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_x, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : m ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0011 : x ∉ ((syn_ctfin (syn_cplc (.cv n) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv m)))) (syn_wne (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_n, fresh_x_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((Wff.imp (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_cevenfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqeq1 (.cv x) M (syn_cplc (.cv n) (.cv n))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) M) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (.classEq M (syn_cplc (.cv n) (.cv n))) n (syn_cnnc) dv_cache_0001 p0000
  have p0002 :=
    @g_neeq1 (.cv x) M (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) M) (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0)) (syn_wne M (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x n dv_cache_0002
  have p0005 :=
    @g_elab2g (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (.cv n) (.cv n)))) (syn_wne M (syn_c0))) x M (syn_cevenfin) (syn_cevenfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem M (syn_cevenfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (.cv n) (.cv n)))) (syn_wne M (syn_c0))) p0005
  have p0007 :=
    @g_addceq2 (.cv n) (syn_c0) (.cv n)
  have p0008 :=
    @g_addcnul1 (.cv n)
  have p0009 :=
    @g_syl6eq (.classEq (.cv n) (syn_c0)) (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv n) (syn_c0)) (syn_c0) p0007 p0008
  have p0010 :=
    @g_necon3i (.cv n) (syn_c0) (syn_cplc (.cv n) (.cv n)) (syn_c0) p0009
  have p0011 :=
    @g_tfinprop (.cv n) x dv_cache_0005
  have p0012 :=
    @g_simpld (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (.cv n) (syn_c0))) (.classMem (syn_ctfin (.cv n)) (syn_cnnc)) (syn_wrex x (.cv n) (.classMem (syn_cpw1 (.cv x)) (syn_ctfin (.cv n)))) p0011
  have p0013 :=
    @g_sylan2 (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (.cv n) (syn_c0)) (.classMem (syn_ctfin (.cv n)) (syn_cnnc)) p0010 p0012
  have p0014 :=
    @g_tfindi (.cv n) (.cv n)
  have p0015 :=
    @g_n_3anidm12 (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n)))) p0014
  have p0016 :=
    @g_addceq12 (.cv m) (.cv m) (syn_ctfin (.cv n)) (syn_ctfin (.cv n))
  have p0017 :=
    @g_anidms (.classEq (.cv m) (syn_ctfin (.cv n))) (.classEq (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n)))) p0016
  have p0018 :=
    @g_eqeq2d (.classEq (.cv m) (syn_ctfin (.cv n))) (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_ctfin (syn_cplc (.cv n) (.cv n))) p0017
  have p0019 :=
    @g_rspcev (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv m))) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n)))) m (syn_ctfin (.cv n)) (syn_cnnc) dv_cache_0006 dv_cache_0007 dv_cache_0008 p0018
  have p0020 :=
    @g_syl2anc (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0))) (.classMem (syn_ctfin (.cv n)) (syn_cnnc)) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n)))) (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv m)))) p0013 p0015 p0019
  have p0021 :=
    @g_nncaddccl (.cv n) (.cv n)
  have p0022 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0021
  have p0023 :=
    @g_tfinnnul (syn_cplc (.cv n) (.cv n))
  have p0024 :=
    @g_sylan (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (syn_wne (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_c0)) p0022 p0023
  have p0025 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0))) (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv m)))) (syn_wne (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_c0)) p0020 p0024
  have p0026 :=
    @g_tfinex (syn_cplc (.cv n) (.cv n))
  have p0027 :=
    @g_eqeq1 (.cv x) (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv m))
  have p0028 :=
    @g_rexbidv (.classEq (.cv x) (syn_ctfin (syn_cplc (.cv n) (.cv n)))) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m))) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv m))) m (syn_cnnc) dv_cache_0009 p0027
  have p0029 :=
    @g_neeq1 (.cv x) (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_c0)
  have p0030 :=
    @g_anbi12d (.classEq (.cv x) (syn_ctfin (syn_cplc (.cv n) (.cv n)))) (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m)))) (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv m)))) (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_c0)) p0028 p0029
  have p0031 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x m dv_cache_0010
  have p0032 :=
    @g_elab2 (syn_wa (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv m)))) (syn_wne (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_c0))) x (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cevenfin) dv_cache_0011 dv_cache_0012 p0026 p0030 p0031
  have p0033 :=
    @g_sylibr (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0))) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv m)))) (syn_wne (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_c0))) (.classMem (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cevenfin)) p0025 p0032
  have p0034 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (.classMem (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cevenfin)) p0033
  have p0035 :=
    @g_neeq1 M (syn_cplc (.cv n) (.cv n)) (syn_c0)
  have p0036 :=
    @g_tfineq M (syn_cplc (.cv n) (.cv n))
  have p0037 :=
    @g_eleq1d (.classEq M (syn_cplc (.cv n) (.cv n))) (syn_ctfin M) (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cevenfin) p0036
  have p0038 :=
    @g_imbi12d (.classEq M (syn_cplc (.cv n) (.cv n))) (syn_wne M (syn_c0)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (.classMem (syn_ctfin M) (syn_cevenfin)) (.classMem (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cevenfin)) p0035 p0037
  have p0039 :=
    @g_biimprd (.classEq M (syn_cplc (.cv n) (.cv n))) (.imp (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_cevenfin))) (.imp (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (.classMem (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cevenfin))) p0038
  have p0040 :=
    @g_com12 (.classEq M (syn_cplc (.cv n) (.cv n))) (.imp (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (.classMem (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cevenfin))) (.imp (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_cevenfin))) p0039
  have p0041 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (.classMem (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cevenfin))) (.imp (.classEq M (syn_cplc (.cv n) (.cv n))) (.imp (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_cevenfin)))) p0034 p0040
  have p0042 :=
    @g_rexlimiv (.classEq M (syn_cplc (.cv n) (.cv n))) (.imp (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_cevenfin))) n (syn_cnnc) dv_cache_0013 p0041
  have p0043 :=
    @g_imp (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (.cv n) (.cv n)))) (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_cevenfin)) p0042
  have p0044 :=
    @g_syl (.classMem M (syn_cevenfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (.cv n) (.cv n)))) (syn_wne M (syn_c0))) (.classMem (syn_ctfin M) (syn_cevenfin)) p0006 p0043
  exact p0044

noncomputable def g_oddtfin
    (M : Class) :
    Nominal.NPrf (.imp (.classMem M (syn_coddfin)) (.classMem (syn_ctfin M) (syn_coddfin))) := by
  let proofSupport : Finset Var := M.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (h)
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (h)
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_x_ne_m : x ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    Ne.symm fresh_x_ne_m
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) M)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne M (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : m ∉ ((syn_ctfin (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : m ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ ((Wff.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : m ∉ ((Wff.classEq (.cv x) (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_x, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : m ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0011 : x ∉ ((syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_n, fresh_x_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((Wff.imp (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_coddfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqeq1 (.cv x) M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) M) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) n (syn_cnnc) dv_cache_0001 p0000
  have p0002 :=
    @g_neeq1 (.cv x) M (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) M) (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0)) (syn_wne M (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x n dv_cache_0002
  have p0005 :=
    @g_elab2g (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne M (syn_c0))) x M (syn_coddfin) (syn_coddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem M (syn_coddfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne M (syn_c0))) p0005
  have p0007 :=
    @g_addceq2 (.cv n) (syn_c0) (.cv n)
  have p0008 :=
    @g_addcnul1 (.cv n)
  have p0009 :=
    @g_syl6eq (.classEq (.cv n) (syn_c0)) (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv n) (syn_c0)) (syn_c0) p0007 p0008
  have p0010 :=
    @g_addceq1 (syn_cplc (.cv n) (.cv n)) (syn_c0) (syn_c1c)
  have p0011 :=
    @g_syl (.classEq (.cv n) (syn_c0)) (.classEq (syn_cplc (.cv n) (.cv n)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cplc (syn_c0) (syn_c1c))) p0009 p0010
  have p0012 :=
    @g_addccom (syn_c0) (syn_c1c)
  have p0013 :=
    @g_addcnul1 (syn_c1c)
  have p0014 :=
    @g_eqtri (syn_cplc (syn_c0) (syn_c1c)) (syn_cplc (syn_c1c) (syn_c0)) (syn_c0) p0012 p0013
  have p0015 :=
    @g_syl6eq (.classEq (.cv n) (syn_c0)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cplc (syn_c0) (syn_c1c)) (syn_c0) p0011 p0014
  have p0016 :=
    @g_necon3i (.cv n) (syn_c0) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0) p0015
  have p0017 :=
    @g_tfinprop (.cv n) x dv_cache_0005
  have p0018 :=
    @g_simpld (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (.cv n) (syn_c0))) (.classMem (syn_ctfin (.cv n)) (syn_cnnc)) (syn_wrex x (.cv n) (.classMem (syn_cpw1 (.cv x)) (syn_ctfin (.cv n)))) p0017
  have p0019 :=
    @g_sylan2 (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (.cv n) (syn_c0)) (.classMem (syn_ctfin (.cv n)) (syn_cnnc)) p0016 p0018
  have p0020 :=
    @g_nncaddccl (.cv n) (.cv n)
  have p0021 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0020
  have p0022 :=
    @g_n_1cnnc
  have p0023 :=
    @g_tfindi (syn_cplc (.cv n) (.cv n)) (syn_c1c)
  have p0024 :=
    @g_mp3an2 (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (.classMem (syn_c1c) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_ctfin (syn_c1c)))) p0022 p0023
  have p0025 :=
    @g_sylan (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_ctfin (syn_c1c)))) p0021 p0024
  have p0026 :=
    @g_addcnnul (syn_cplc (.cv n) (.cv n)) (syn_c1c)
  have p0027 :=
    @g_simpld (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (syn_wne (syn_c1c) (syn_c0)) p0026
  have p0028 :=
    @g_tfindi (.cv n) (.cv n)
  have p0029 :=
    @g_n_3anidm12 (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n)))) p0028
  have p0030 :=
    @g_sylan2 (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n)))) p0027 p0029
  have p0031 :=
    @g_tfin1c
  have p0032 :=
    @g_addceq12 (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_ctfin (syn_c1c)) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_c1c)
  have p0033 :=
    @g_mpan2 (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n)))) (.classEq (syn_ctfin (syn_c1c)) (syn_c1c)) (.classEq (syn_cplc (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_ctfin (syn_c1c))) (syn_cplc (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_c1c))) p0031 p0032
  have p0034 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (.classEq (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n)))) (.classEq (syn_cplc (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_ctfin (syn_c1c))) (syn_cplc (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_c1c))) p0030 p0033
  have p0035 :=
    @g_eqtrd (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_ctfin (syn_cplc (.cv n) (.cv n))) (syn_ctfin (syn_c1c))) (syn_cplc (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_c1c)) p0025 p0034
  have p0036 :=
    @g_addceq12 (.cv m) (.cv m) (syn_ctfin (.cv n)) (syn_ctfin (.cv n))
  have p0037 :=
    @g_anidms (.classEq (.cv m) (syn_ctfin (.cv n))) (.classEq (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n)))) p0036
  have p0038 :=
    @g_addceq1 (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_c1c)
  have p0039 :=
    @g_syl (.classEq (.cv m) (syn_ctfin (.cv n))) (.classEq (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n)))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_c1c))) p0037 p0038
  have p0040 :=
    @g_eqeq2d (.classEq (.cv m) (syn_ctfin (.cv n))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_c1c)) (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) p0039
  have p0041 :=
    @g_rspcev (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_c1c))) m (syn_ctfin (.cv n)) (syn_cnnc) dv_cache_0006 dv_cache_0007 dv_cache_0008 p0040
  have p0042 :=
    @g_syl2anc (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (.classMem (syn_ctfin (.cv n)) (syn_cnnc)) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (syn_ctfin (.cv n)) (syn_ctfin (.cv n))) (syn_c1c))) (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) p0019 p0035 p0041
  have p0043 :=
    @g_peano2 (syn_cplc (.cv n) (.cv n))
  have p0044 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cnnc)) p0021 p0043
  have p0045 :=
    @g_tfinnnul (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0046 :=
    @g_sylan (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_c0)) p0044 p0045
  have p0047 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_c0)) p0042 p0046
  have p0048 :=
    @g_tfinex (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0049 :=
    @g_eqeq1 (.cv x) (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))
  have p0050 :=
    @g_rexbidv (.classEq (.cv x) (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))) m (syn_cnnc) dv_cache_0009 p0049
  have p0051 :=
    @g_neeq1 (.cv x) (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_c0)
  have p0052 :=
    @g_anbi12d (.classEq (.cv x) (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_c0)) p0050 p0051
  have p0053 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x m dv_cache_0010
  have p0054 :=
    @g_elab2 (syn_wa (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_c0))) x (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_coddfin) dv_cache_0011 dv_cache_0012 p0048 p0052 p0053
  have p0055 :=
    @g_sylibr (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_c0))) (.classMem (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_coddfin)) p0047 p0054
  have p0056 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classMem (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_coddfin)) p0055
  have p0057 :=
    @g_neeq1 M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)
  have p0058 :=
    @g_tfineq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0059 :=
    @g_eleq1d (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_ctfin M) (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_coddfin) p0058
  have p0060 :=
    @g_imbi12d (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne M (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classMem (syn_ctfin M) (syn_coddfin)) (.classMem (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_coddfin)) p0057 p0059
  have p0061 :=
    @g_biimprd (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.imp (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_coddfin))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classMem (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_coddfin))) p0060
  have p0062 :=
    @g_com12 (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classMem (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_coddfin))) (.imp (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_coddfin))) p0061
  have p0063 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classMem (syn_ctfin (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_coddfin))) (.imp (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.imp (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_coddfin)))) p0056 p0062
  have p0064 :=
    @g_rexlimiv (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.imp (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_coddfin))) n (syn_cnnc) dv_cache_0013 p0063
  have p0065 :=
    @g_imp (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_coddfin)) p0064
  have p0066 :=
    @g_syl (.classMem M (syn_coddfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq M (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne M (syn_c0))) (.classMem (syn_ctfin M) (syn_coddfin)) p0006 p0065
  exact p0066

#print axioms g_oddtfin

end NFChoice.DirectNominalPrf.WPPReplay
