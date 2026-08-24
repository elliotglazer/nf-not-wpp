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
import NominalWPPReplayChunk010Compact001Part014

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

noncomputable def g_sfintfin
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wsfin M N) (syn_wsfin (syn_ctfin M) (syn_ctfin N))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let k : Var := freshVar proofSupport 2
  let m : Var := freshVar proofSupport 3
  let p : Var := freshVar proofSupport 4
  let q : Var := freshVar proofSupport 5
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_k_not_M : k ∉ M.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (h))
  have fresh_k_not_N : k ∉ N.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (h))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_a_ne_n : a ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_a : n ≠ a :=
    Ne.symm fresh_a_ne_n
  have fresh_a_ne_k : a ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_k_ne_a : k ≠ a :=
    Ne.symm fresh_a_ne_k
  have fresh_a_ne_m : a ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_m_ne_a : m ≠ a :=
    Ne.symm fresh_a_ne_m
  have fresh_a_ne_p : a ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_p_ne_a : p ≠ a :=
    Ne.symm fresh_a_ne_p
  have fresh_a_ne_q : a ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_q_ne_a : q ≠ a :=
    Ne.symm fresh_a_ne_q
  have fresh_n_ne_k : n ≠ k := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_k_ne_n : k ≠ n :=
    Ne.symm fresh_n_ne_k
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_n_ne_p : n ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_p_ne_n : p ≠ n :=
    Ne.symm fresh_n_ne_p
  have fresh_n_ne_q : n ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_q_ne_n : q ≠ n :=
    Ne.symm fresh_n_ne_q
  have fresh_k_ne_m : k ≠ m := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_m_ne_k : m ≠ k :=
    Ne.symm fresh_k_ne_m
  have fresh_k_ne_p : k ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_p_ne_k : p ≠ k :=
    Ne.symm fresh_k_ne_p
  have fresh_k_ne_q : k ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_q_ne_k : q ≠ k :=
    Ne.symm fresh_k_ne_q
  have fresh_m_ne_p : m ≠ p := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_p_ne_m : p ≠ m :=
    Ne.symm fresh_m_ne_p
  have fresh_m_ne_q : m ≠ q := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_q_ne_m : q ≠ m :=
    Ne.symm fresh_m_ne_q
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : a ∉ (M).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (N).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : k ≠ n := by
    clear dv_cache_0001 dv_cache_0002
    exact (show k ≠ n from (by exact fresh_k_ne_n))
  have dv_cache_0004 : n ∉ ((Wff.classEq (.cv k) (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.objEq k m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((Wff.imp (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_m, fresh_p_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Wff.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((Wff.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((Wff.classEq (.cv k) M)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_k, fresh_n_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_cplc (.cv m) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((Wff.imp (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_m, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((syn_cplc (.cv q) (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((syn_ctfin (.cv m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ ((syn_ctfin (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : k ∉ ((syn_ctfin (.cv m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : k ∉ ((syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_m, fresh_k_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : k ∉ ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_m, fresh_k_ne_n, fresh_k_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, fresh_a_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : a ∉ ((syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : a ∉ ((syn_wne (syn_cplc (.cv q) (.cv q)) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : q ∉ ((syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_m, fresh_q_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : q ∉ ((syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_m, fresh_q_ne_n, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : a ∉ ((syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, fresh_a_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : n ∉ ((syn_wa (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : k ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : k ∉ ((Wff.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_m, fresh_k_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : m ∉ ((Wff.all n (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_k, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : k ∉ ((Wff.all n (.imp (syn_wsfin (syn_c0c) (.cv n)) (syn_wsfin (syn_c0c) (syn_ctfin (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : k ∉ ((Wff.all n (.imp (syn_wsfin M (.cv n)) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_M, fresh_k_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : k ∉ ((Wff.all n (.imp (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_m, fresh_k_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : k ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show k ≠ m from (by exact fresh_k_ne_m))
  have dv_cache_0036 : n ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : n ∉ ((Wff.imp (syn_wsfin M N) (syn_wsfin (syn_ctfin M) (syn_ctfin N)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_M, fresh_n_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M N a dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_n_3simpa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N)))
  have p0002 :=
    @g_sylbi (syn_wsfin M N) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N)))) (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) p0000 p0001
  have p0003 :=
    @g_sfintfinlem1 k n dv_cache_0003
  have p0004 :=
    @g_sfineq1 (.cv k) (syn_c0c) (.cv n)
  have p0005 :=
    @g_tfineq (.cv k) (syn_c0c)
  have p0006 :=
    @g_tfin0c
  have p0007 :=
    @g_syl6eq (.classEq (.cv k) (syn_c0c)) (syn_ctfin (.cv k)) (syn_ctfin (syn_c0c)) (syn_c0c) p0005 p0006
  have p0008 :=
    @g_sfineq1 (syn_ctfin (.cv k)) (syn_c0c) (syn_ctfin (.cv n))
  have p0009 :=
    @g_syl (.classEq (.cv k) (syn_c0c)) (.classEq (syn_ctfin (.cv k)) (syn_c0c)) (syn_wb (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))) (syn_wsfin (syn_c0c) (syn_ctfin (.cv n)))) p0007 p0008
  have p0010 :=
    @g_imbi12d (.classEq (.cv k) (syn_c0c)) (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_c0c) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))) (syn_wsfin (syn_c0c) (syn_ctfin (.cv n))) p0004 p0009
  have p0011 :=
    @g_albidv (.classEq (.cv k) (syn_c0c)) (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))) (.imp (syn_wsfin (syn_c0c) (.cv n)) (syn_wsfin (syn_c0c) (syn_ctfin (.cv n)))) n dv_cache_0004 p0010
  have p0012 :=
    @g_sfineq1 (.cv k) (.cv m) (.cv n)
  have p0013 :=
    @g_tfineq (.cv k) (.cv m)
  have p0014 :=
    @g_sfineq1 (syn_ctfin (.cv k)) (syn_ctfin (.cv m)) (syn_ctfin (.cv n))
  have p0015_e00_recanon : Nominal.NPrf (.imp (.objEq k m) (.classEq (syn_ctfin (.cv k)) (syn_ctfin (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0013
  have p0015 :=
    @g_syl (.objEq k m) (.classEq (syn_ctfin (.cv k)) (syn_ctfin (.cv m))) (syn_wb (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))) p0015_e00_recanon p0014
  have p0016_e00_recanon : Nominal.NPrf (.imp (.objEq k m) (syn_wb (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (.cv m) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0012
  have p0016 :=
    @g_imbi12d (.objEq k m) (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))) p0016_e00_recanon p0015
  have p0017 :=
    @g_albidv (.objEq k m) (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))) (.imp (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))) n dv_cache_0005 p0016
  have p0018 :=
    @g_sfineq2 (.cv n) (.cv p) (.cv m)
  have p0019 :=
    @g_tfineq (.cv n) (.cv p)
  have p0020 :=
    @g_sfineq2 (syn_ctfin (.cv n)) (syn_ctfin (.cv p)) (syn_ctfin (.cv m))
  have p0021_e00_recanon : Nominal.NPrf (.imp (.objEq n p) (.classEq (syn_ctfin (.cv n)) (syn_ctfin (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0019
  have p0021 :=
    @g_syl (.objEq n p) (.classEq (syn_ctfin (.cv n)) (syn_ctfin (.cv p))) (syn_wb (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))) p0021_e00_recanon p0020
  have p0022_e00_recanon : Nominal.NPrf (.imp (.objEq n p) (syn_wb (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (.cv m) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0018
  have p0022 :=
    @g_imbi12d (.objEq n p) (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))) p0022_e00_recanon p0021
  have p0023 :=
    @g_cbvalv (.imp (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))) (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))) n p dv_cache_0006 dv_cache_0007 p0022
  have p0024 :=
    @g_syl6bb (.objEq k m) (.all n (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))))) (.all n (.imp (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))))) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) p0017 p0023
  have p0025 :=
    @g_sfineq1 (.cv k) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0026 :=
    @g_tfineq (.cv k) (syn_cplc (.cv m) (syn_c1c))
  have p0027 :=
    @g_sfineq1 (syn_ctfin (.cv k)) (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))
  have p0028 :=
    @g_syl (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (.classEq (syn_ctfin (.cv k)) (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))) (syn_wb (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))) p0026 p0027
  have p0029 :=
    @g_imbi12d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0025 p0028
  have p0030 :=
    @g_albidv (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))) (.imp (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))) n dv_cache_0008 p0029
  have p0031 :=
    @g_sfineq1 (.cv k) M (.cv n)
  have p0032 :=
    @g_tfineq (.cv k) M
  have p0033 :=
    @g_sfineq1 (syn_ctfin (.cv k)) (syn_ctfin M) (syn_ctfin (.cv n))
  have p0034 :=
    @g_syl (.classEq (.cv k) M) (.classEq (syn_ctfin (.cv k)) (syn_ctfin M)) (syn_wb (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n)))) p0032 p0033
  have p0035 :=
    @g_imbi12d (.classEq (.cv k) M) (syn_wsfin (.cv k) (.cv n)) (syn_wsfin M (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n))) p0031 p0034
  have p0036 :=
    @g_albidv (.classEq (.cv k) M) (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))) (.imp (syn_wsfin M (.cv n)) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n)))) n dv_cache_0009 p0035
  have p0037 :=
    @g_sfin01
  have p0038 :=
    @g_sfin112 (syn_c1c) (syn_c0c) (.cv n)
  have p0039 :=
    @g_mpan2 (syn_wsfin (syn_c0c) (.cv n)) (syn_wsfin (syn_c0c) (syn_c1c)) (.classEq (.cv n) (syn_c1c)) p0037 p0038
  have p0040 :=
    @g_sfin01
  have p0041 :=
    @g_tfineq (.cv n) (syn_c1c)
  have p0042 :=
    @g_tfin1c
  have p0043 :=
    @g_syl6eq (.classEq (.cv n) (syn_c1c)) (syn_ctfin (.cv n)) (syn_ctfin (syn_c1c)) (syn_c1c) p0041 p0042
  have p0044 :=
    @g_sfineq2 (syn_ctfin (.cv n)) (syn_c1c) (syn_c0c)
  have p0045 :=
    @g_syl (.classEq (.cv n) (syn_c1c)) (.classEq (syn_ctfin (.cv n)) (syn_c1c)) (syn_wb (syn_wsfin (syn_c0c) (syn_ctfin (.cv n))) (syn_wsfin (syn_c0c) (syn_c1c))) p0043 p0044
  have p0046 :=
    @g_mpbiri (.classEq (.cv n) (syn_c1c)) (syn_wsfin (syn_c0c) (syn_ctfin (.cv n))) (syn_wsfin (syn_c0c) (syn_c1c)) p0040 p0045
  have p0047 :=
    @g_syl (syn_wsfin (syn_c0c) (.cv n)) (.classEq (.cv n) (syn_c1c)) (syn_wsfin (syn_c0c) (syn_ctfin (.cv n))) p0039 p0046
  have p0048 :=
    Nominal.gen p0047 n
  have p0049 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin (syn_cplc (.cv m) (syn_c1c)) (.cv n) a dv_cache_0010 dv_cache_0011
  have p0050 :=
    @g_simp3bi (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (.cv n)))) p0049
  have p0051 :=
    @g_n_3ad2ant3 (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (.cv m) (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (.cv n)))) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) p0050
  have p0052 :=
    @g_sfindbl (.cv a) q (.cv m) dv_cache_0012
  have p0053 :=
    @g_n_3ad2antl1 (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (syn_wrex q (syn_cnnc) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0052
  have p0054 :=
    @g_sfineq2 (.cv p) (.cv q) (.cv m)
  have p0055 :=
    @g_tfineq (.cv p) (.cv q)
  have p0056 :=
    @g_sfineq2 (syn_ctfin (.cv p)) (syn_ctfin (.cv q)) (syn_ctfin (.cv m))
  have p0057_e00_recanon : Nominal.NPrf (.imp (.objEq p q) (.classEq (syn_ctfin (.cv p)) (syn_ctfin (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0055
  have p0057 :=
    @g_syl (.objEq p q) (.classEq (syn_ctfin (.cv p)) (syn_ctfin (.cv q))) (syn_wb (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) p0057_e00_recanon p0056
  have p0058_e00_recanon : Nominal.NPrf (.imp (.objEq p q) (syn_wb (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (.cv m) (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0054
  have p0058 :=
    @g_imbi12d (.objEq p q) (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) p0058_e00_recanon p0057
  have p0059 :=
    @g_spv (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))) (.imp (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) p q dv_cache_0013 p0058
  have p0060 :=
    @g_simprrl (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (.cv q) (syn_cnnc)) (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))
  have p0061 :=
    @g_adantl (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))) (syn_wsfin (.cv m) (.cv q)) (.classMem (.cv m) (syn_cnnc)) p0060
  have p0062 :=
    @g_simplrl (.classMem (.cv m) (syn_cnnc)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
  have p0063 :=
    @g_simprrr (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (.cv q) (syn_cnnc)) (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))
  have p0064 :=
    @g_ad2antlr (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))) (.classMem (.cv m) (syn_cnnc)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) p0063
  have p0065 :=
    @g_sfin112 (syn_cplc (.cv q) (.cv q)) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0066 :=
    @g_syl2anc (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))) (.classEq (.cv n) (syn_cplc (.cv q) (.cv q))) p0062 p0064 p0065
  have p0067 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)) a dv_cache_0010 dv_cache_0014
  have p0068 :=
    @g_simp3bi (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc (.cv q) (.cv q)) (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))))) p0067
  have p0069 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))))) p0064 p0068
  have p0070 :=
    @g_simp2 (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
  have p0071 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)) a dv_cache_0015 dv_cache_0016
  have p0072 :=
    @g_simp1bi (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_ctfin (.cv m)) (syn_cnnc)) (.classMem (syn_ctfin (.cv q)) (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (.cv m))) (.classMem (syn_cpw (.cv a)) (syn_ctfin (.cv q))))) p0071
  have p0073 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_ctfin (.cv m)) (syn_cnnc)) p0070 p0072
  have p0074 :=
    @g_simp1l (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
  have p0075 :=
    @g_peano2 (.cv m)
  have p0076 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) p0074 p0075
  have p0077 :=
    @g_simp3 (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
  have p0078 :=
    @g_tfinpw1 (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))
  have p0079 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw1 (syn_cpw1 (.cv a))) (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))) p0076 p0077 p0078
  have p0080 :=
    @g_ne0i (syn_cplc (.cv m) (syn_c1c)) (syn_cpw1 (.cv a))
  have p0081 :=
    @g_n_3ad2ant3 (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) p0080
  have p0082 :=
    @g_tfinsuc (.cv m)
  have p0083 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))) (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))) p0074 p0081 p0082
  have p0084 :=
    @g_eleqtrd (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))) (syn_cpw1 (syn_cpw1 (.cv a))) (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) p0079 p0083
  have p0085 :=
    @g_sfindbl (syn_cpw1 (.cv a)) k (syn_ctfin (.cv m)) dv_cache_0017
  have p0086 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))) (.classMem (syn_ctfin (.cv m)) (syn_cnnc)) (.classMem (syn_cpw1 (syn_cpw1 (.cv a))) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))) (syn_wrex k (syn_cnnc) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))) p0073 p0084 p0085
  have p0087 :=
    @g_simp2 (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))
  have p0088 :=
    @g_simp3l (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))
  have p0089 :=
    @g_sfin112 (.cv k) (syn_ctfin (.cv m)) (syn_ctfin (.cv q))
  have p0090 :=
    @g_syl2anc (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (.classEq (syn_ctfin (.cv q)) (.cv k)) p0087 p0088 p0089
  have p0091 :=
    @g_addceq12 (syn_ctfin (.cv q)) (syn_ctfin (.cv q)) (.cv k) (.cv k)
  have p0092 :=
    @g_anidms (.classEq (syn_ctfin (.cv q)) (.cv k)) (.classEq (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))) (syn_cplc (.cv k) (.cv k))) p0091
  have p0093 :=
    @g_sfineq2 (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))) (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
  have p0094 :=
    @g_syl (.classEq (syn_ctfin (.cv q)) (.cv k)) (.classEq (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))) (syn_cplc (.cv k) (.cv k))) (syn_wb (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))) p0092 p0093
  have p0095 :=
    @g_biimprcd (.classEq (syn_ctfin (.cv q)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))) p0094
  have p0096 :=
    @g_adantl (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))) (.imp (.classEq (syn_ctfin (.cv q)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))) (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) p0095
  have p0097 :=
    @g_n_3ad2ant3 (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (.imp (.classEq (syn_ctfin (.cv q)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) p0096
  have p0098 :=
    @g_mpd (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))) (.classEq (syn_ctfin (.cv q)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) p0090 p0097
  have p0099 :=
    @g_n_3expia (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) p0098
  have p0100 :=
    @g_rexlimdvw (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) k (syn_cnnc) dv_cache_0018 dv_cache_0019 p0099
  have p0101 :=
    @g_n_3adant3 (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.imp (syn_wrex k (syn_cnnc) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) p0100
  have p0102 :=
    @g_mpd (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))) (syn_wrex k (syn_cnnc) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) p0086 p0101
  have p0103 :=
    @g_n_3expia (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) p0102
  have p0104 :=
    @g_adantrd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))) p0103
  have p0105 :=
    @g_exlimdv (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q)))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) a dv_cache_0020 dv_cache_0021 p0104
  have p0106 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) p0069 p0105
  have p0107 :=
    @g_simpll (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
  have p0108 :=
    @g_adantr (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))) p0080
  have p0109 :=
    @g_exlimiv (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q)))) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) a dv_cache_0022 p0108
  have p0110 :=
    @g_n_3syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))))) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0064 p0068 p0109
  have p0111 :=
    @g_syl2anc (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))) p0107 p0110 p0082
  have p0112 :=
    @g_simprrl (.classMem (.cv m) (syn_cnnc)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))
  have p0113 :=
    @g_adantr (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (.classMem (.cv q) (syn_cnnc)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) p0112
  have p0114 :=
    @g_ne0i (syn_cplc (.cv q) (.cv q)) (syn_cpw (.cv a))
  have p0115 :=
    @g_adantl (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))) (syn_wne (syn_cplc (.cv q) (.cv q)) (syn_c0)) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) p0114
  have p0116 :=
    @g_exlimiv (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q)))) (syn_wne (syn_cplc (.cv q) (.cv q)) (syn_c0)) a dv_cache_0023 p0115
  have p0117 :=
    @g_n_3syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))))) (syn_wne (syn_cplc (.cv q) (.cv q)) (syn_c0)) p0064 p0068 p0116
  have p0118 :=
    @g_tfindi (.cv q) (.cv q)
  have p0119 :=
    @g_syl3anc (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (.classMem (.cv q) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc)) (syn_wne (syn_cplc (.cv q) (.cv q)) (syn_c0)) (.classEq (syn_ctfin (syn_cplc (.cv q) (.cv q))) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) p0113 p0113 p0117 p0118
  have p0120 :=
    @g_sfineq1 (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_ctfin (syn_cplc (.cv q) (.cv q)))
  have p0121 :=
    @g_sfineq2 (syn_ctfin (syn_cplc (.cv q) (.cv q))) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
  have p0122 :=
    @g_sylan9bb (.classEq (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (syn_cplc (.cv q) (.cv q)))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_ctfin (syn_cplc (.cv q) (.cv q)))) (.classEq (syn_ctfin (syn_cplc (.cv q) (.cv q))) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) p0120 p0121
  have p0123 :=
    @g_syl2anc (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (.classEq (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))) (.classEq (syn_ctfin (syn_cplc (.cv q) (.cv q))) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) (syn_wb (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (syn_cplc (.cv q) (.cv q)))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))) p0111 p0119 p0122
  have p0124 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (syn_cplc (.cv q) (.cv q)))) (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))) p0106 p0123
  have p0125 :=
    @g_tfineq (.cv n) (syn_cplc (.cv q) (.cv q))
  have p0126 :=
    @g_sfineq2 (syn_ctfin (.cv n)) (syn_ctfin (syn_cplc (.cv q) (.cv q))) (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
  have p0127 :=
    @g_syl (.classEq (.cv n) (syn_cplc (.cv q) (.cv q))) (.classEq (syn_ctfin (.cv n)) (syn_ctfin (syn_cplc (.cv q) (.cv q)))) (syn_wb (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (syn_cplc (.cv q) (.cv q))))) p0125 p0126
  have p0128 :=
    @g_biimprcd (.classEq (.cv n) (syn_cplc (.cv q) (.cv q))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (syn_cplc (.cv q) (.cv q)))) p0127
  have p0129 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (syn_cplc (.cv q) (.cv q)))) (.imp (.classEq (.cv n) (syn_cplc (.cv q) (.cv q))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))) p0124 p0128
  have p0130 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (.classEq (.cv n) (syn_cplc (.cv q) (.cv q))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0066 p0129
  have p0131 :=
    @g_ex (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0130
  have p0132 :=
    @g_embantd (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0061 p0131
  have p0133 :=
    @g_syl5 (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (.imp (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0059 p0132
  have p0134 :=
    @g_exp32 (.classMem (.cv m) (syn_cnnc)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))) (.imp (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))) p0133
  have p0135 :=
    @g_com34 (.classMem (.cv m) (syn_cnnc)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0134
  have p0136 :=
    @g_com23 (.classMem (.cv m) (syn_cnnc)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (.imp (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))) p0135
  have p0137 :=
    @g_n_3imp (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.imp (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))) p0136
  have p0138 :=
    @g_exp3a (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0137
  have p0139 :=
    @g_rexlimdv (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) q (syn_cnnc) dv_cache_0024 dv_cache_0025 p0138
  have p0140 :=
    @g_adantr (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (.imp (syn_wrex q (syn_cnnc) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) p0139
  have p0141 :=
    @g_mpd (syn_wa (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))) (syn_wrex q (syn_cnnc) (syn_wa (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0053 p0140
  have p0142 :=
    @g_ex (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0141
  have p0143 :=
    @g_adantrd (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) (.classMem (syn_cpw (.cv a)) (.cv n)) p0142
  have p0144 :=
    @g_exlimdv (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (.cv n))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) a dv_cache_0026 dv_cache_0027 p0143
  have p0145 :=
    @g_mpd (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cpw (.cv a)) (.cv n)))) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0051 p0144
  have p0146 :=
    @g_n_3expia (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0145
  have p0147 :=
    @g_alrimiv (syn_wa (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))) (.imp (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))) n dv_cache_0028 p0146
  have p0148 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (.all n (.imp (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))))) p0147
  have p0149 :=
    @g_finds (.all n (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))))) (.all n (.imp (syn_wsfin (syn_c0c) (.cv n)) (syn_wsfin (syn_c0c) (syn_ctfin (.cv n))))) (.all p (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))) (.all n (.imp (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))))) (.all n (.imp (syn_wsfin M (.cv n)) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n))))) k m M dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 p0003 p0011 p0024 p0030 p0036 p0048 p0148
  have p0150 :=
    @g_sfineq2 (.cv n) N M
  have p0151 :=
    @g_tfineq (.cv n) N
  have p0152 :=
    @g_sfineq2 (syn_ctfin (.cv n)) (syn_ctfin N) (syn_ctfin M)
  have p0153 :=
    @g_syl (.classEq (.cv n) N) (.classEq (syn_ctfin (.cv n)) (syn_ctfin N)) (syn_wb (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin M) (syn_ctfin N))) p0151 p0152
  have p0154 :=
    @g_imbi12d (.classEq (.cv n) N) (syn_wsfin M (.cv n)) (syn_wsfin M N) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin M) (syn_ctfin N)) p0150 p0153
  have p0155 :=
    @g_spcgv (.imp (syn_wsfin M (.cv n)) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n)))) (.imp (syn_wsfin M N) (syn_wsfin (syn_ctfin M) (syn_ctfin N))) n N (syn_cnnc) dv_cache_0036 dv_cache_0037 p0154
  have p0156 :=
    @g_mpan9 (.classMem M (syn_cnnc)) (.all n (.imp (syn_wsfin M (.cv n)) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n))))) (.classMem N (syn_cnnc)) (.imp (syn_wsfin M N) (syn_wsfin (syn_ctfin M) (syn_ctfin N))) p0149 p0155
  have p0157 :=
    @g_mpcom (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wsfin M N) (syn_wsfin (syn_ctfin M) (syn_ctfin N)) p0002 p0156
  exact p0157

#print axioms g_sfintfin

end NFChoice.DirectNominalPrf.WPPReplay
