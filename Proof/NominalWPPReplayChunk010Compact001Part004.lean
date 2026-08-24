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
import NominalWPPReplayChunk010Compact001Part003

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

noncomputable def g_evenodddisj
     :
    Nominal.NPrf (.classEq (syn_cin (syn_cevenfin) (syn_coddfin)) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let j : Var := freshVar proofSupport 3
  let m : Var := freshVar proofSupport 4
  let p : Var := freshVar proofSupport 5
  let q : Var := freshVar proofSupport 6
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_j : j ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_x_ne_k : x ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_k_ne_x : k ≠ x :=
    Ne.symm fresh_x_ne_k
  have fresh_x_ne_n : x ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_x : n ≠ x :=
    Ne.symm fresh_x_ne_n
  have fresh_x_ne_j : x ≠ j := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_j_ne_x : j ≠ x :=
    Ne.symm fresh_x_ne_j
  have fresh_x_ne_m : x ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    Ne.symm fresh_x_ne_m
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_k_ne_n : k ≠ n := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_k : n ≠ k :=
    Ne.symm fresh_k_ne_n
  have fresh_k_ne_j : k ≠ j := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_j_ne_k : j ≠ k :=
    Ne.symm fresh_k_ne_j
  have fresh_k_ne_m : k ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_m_ne_k : m ≠ k :=
    Ne.symm fresh_k_ne_m
  have fresh_k_ne_p : k ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_p_ne_k : p ≠ k :=
    Ne.symm fresh_k_ne_p
  have fresh_k_ne_q : k ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_q_ne_k : q ≠ k :=
    Ne.symm fresh_k_ne_q
  have fresh_n_ne_j : n ≠ j := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_j_ne_n : j ≠ n :=
    Ne.symm fresh_n_ne_j
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_n_ne_p : n ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_p_ne_n : p ≠ n :=
    Ne.symm fresh_n_ne_p
  have fresh_n_ne_q : n ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_q_ne_n : q ≠ n :=
    Ne.symm fresh_n_ne_q
  have fresh_j_ne_m : j ≠ m := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_m_ne_j : m ≠ j :=
    Ne.symm fresh_j_ne_m
  have fresh_j_ne_p : j ≠ p := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_p_ne_j : p ≠ j :=
    Ne.symm fresh_j_ne_p
  have fresh_j_ne_q : j ≠ q := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_q_ne_j : q ≠ j :=
    Ne.symm fresh_j_ne_q
  have fresh_m_ne_p : m ≠ p := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_p_ne_m : p ≠ m :=
    Ne.symm fresh_m_ne_p
  have fresh_m_ne_q : m ≠ q := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_q_ne_m : q ≠ m :=
    Ne.symm fresh_m_ne_q
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : k ≠ x := by
    exact (show k ≠ x from (by exact fresh_k_ne_x))
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : j ≠ n := by
    clear dv_cache_0001 dv_cache_0002
    exact (show j ≠ n from (by exact fresh_j_ne_n))
  have dv_cache_0004 : n ∉ ((Wff.classEq (.cv j) (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_j, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.objEq j m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_j, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((Wff.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_n, fresh_p_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((Wff.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_p, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : n ∉ ((Wff.classEq (.cv j) (syn_cplc (.cv m) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_j, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((Wff.objEq j k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_j, fresh_n_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((Wff.imp (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, fresh_p_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : q ∉ ((Wff.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_m, fresh_q_ne_p, fresh_q_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : n ∉ ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : j ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_j_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : j ∉ ((Wff.imp (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_c0)) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_j_ne_m, fresh_j_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : m ∉ ((Wff.imp (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_j, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : j ∉ ((Wff.imp (syn_wne (syn_c0c) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_j_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : j ∉ ((Wff.imp (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_j_ne_k, fresh_j_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : j ∉ ((Wff.imp (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_j_ne_m, fresh_j_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : j ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show j ≠ m from (by exact fresh_j_ne_m))
  have dv_cache_0024 : n ∉ ((Wff.classEq (.cv x) (syn_cplc (.cv k) (.cv k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, fresh_n_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : k ∉ ((Wff.neg (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_x, fresh_k_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dfevenfin2 x k dv_cache_0001
  have p0001 :=
    @g_dfoddfin2 x n dv_cache_0002
  have p0002 :=
    @g_ineq12i (syn_cevenfin) (.cab x (syn_wrex k (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0))))) (syn_coddfin) (.cab x (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))) p0000 p0001
  have p0003 :=
    @g_inab (syn_wrex k (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) x
  have p0004 :=
    @g_eqtri (syn_cin (syn_cevenfin) (syn_coddfin)) (syn_cin (.cab x (syn_wrex k (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0))))) (.cab x (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))) (.cab x (syn_wa (syn_wrex k (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))) p0002 p0003
  have p0005 :=
    @g_evenodddisjlem1 j n dv_cache_0003
  have p0006 :=
    @g_addceq12 (.cv j) (.cv j) (syn_c0c) (syn_c0c)
  have p0007 :=
    @g_anidms (.classEq (.cv j) (syn_c0c)) (.classEq (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_c0c) (syn_c0c))) p0006
  have p0008 :=
    @g_addcid2 (syn_c0c)
  have p0009 :=
    @g_syl6eq (.classEq (.cv j) (syn_c0c)) (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c) p0007 p0008
  have p0010 :=
    @g_neeq1d (.classEq (.cv j) (syn_c0c)) (syn_cplc (.cv j) (.cv j)) (syn_c0c) (syn_c0) p0009
  have p0011 :=
    @g_neeq1d (.classEq (.cv j) (syn_c0c)) (syn_cplc (.cv j) (.cv j)) (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) p0009
  have p0012 :=
    @g_imbi2d (.classEq (.cv j) (syn_c0c)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0011
  have p0013 :=
    @g_ralbidv (.classEq (.cv j) (syn_c0c)) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) n (syn_cnnc) dv_cache_0004 p0012
  have p0014 :=
    @g_imbi12d (.classEq (.cv j) (syn_c0c)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0)) (syn_wne (syn_c0c) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) p0010 p0013
  have p0015 :=
    @g_addceq12 (.cv j) (.cv j) (.cv m) (.cv m)
  have p0016_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objEq j m) (.objEq j m)) (.classEq (syn_cplc (.cv j) (.cv j)) (syn_cplc (.cv m) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cplc syn_wrex syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0015
  have p0016 :=
    @g_anidms (.objEq j m) (.classEq (syn_cplc (.cv j) (.cv j)) (syn_cplc (.cv m) (.cv m))) p0016_e00_recanon
  have p0017 :=
    @g_neeq1d (.objEq j m) (syn_cplc (.cv j) (.cv j)) (syn_cplc (.cv m) (.cv m)) (syn_c0) p0016
  have p0018 :=
    @g_neeq1d (.objEq j m) (syn_cplc (.cv j) (.cv j)) (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) p0016
  have p0019 :=
    @g_imbi2d (.objEq j m) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0018
  have p0020 :=
    @g_ralbidv (.objEq j m) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) n (syn_cnnc) dv_cache_0005 p0019
  have p0021 :=
    @g_addceq12 (.cv n) (.cv n) (.cv p) (.cv p)
  have p0022_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objEq n p) (.objEq n p)) (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv p) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cplc syn_wrex syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0021
  have p0022 :=
    @g_anidms (.objEq n p) (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv p) (.cv p))) p0022_e00_recanon
  have p0023 :=
    @g_addceq1d (.objEq n p) (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv p) (.cv p)) (syn_c1c) p0022
  have p0024 :=
    @g_neeq1d (.objEq n p) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0) p0023
  have p0025 :=
    @g_neeq2d (.objEq n p) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_cplc (.cv m) (.cv m)) p0023
  have p0026 :=
    @g_imbi12d (.objEq n p) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))) p0024 p0025
  have p0027 :=
    @g_cbvralv (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))) n p (syn_cnnc) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0026
  have p0028 :=
    @g_syl6bb (.objEq j m) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) p0020 p0027
  have p0029 :=
    @g_imbi12d (.objEq j m) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) p0017 p0028
  have p0030 :=
    @g_addceq12 (.cv j) (.cv j) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))
  have p0031 :=
    @g_anidms (.classEq (.cv j) (syn_cplc (.cv m) (syn_c1c))) (.classEq (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))) p0030
  have p0032 :=
    @g_addcass (syn_cplc (.cv m) (syn_c1c)) (.cv m) (syn_c1c)
  have p0033 :=
    @g_addc32 (.cv m) (syn_c1c) (.cv m)
  have p0034 :=
    @g_addceq1i (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c) p0033
  have p0035 :=
    @g_eqtr3i (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) p0032 p0034
  have p0036 :=
    @g_syl6eq (.classEq (.cv j) (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) p0031 p0035
  have p0037 :=
    @g_neeq1d (.classEq (.cv j) (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0) p0036
  have p0038 :=
    @g_neeq1d (.classEq (.cv j) (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) p0036
  have p0039 :=
    @g_imbi2d (.classEq (.cv j) (syn_cplc (.cv m) (syn_c1c))) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0038
  have p0040 :=
    @g_ralbidv (.classEq (.cv j) (syn_cplc (.cv m) (syn_c1c))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) n (syn_cnnc) dv_cache_0010 p0039
  have p0041 :=
    @g_imbi12d (.classEq (.cv j) (syn_cplc (.cv m) (syn_c1c))) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) p0037 p0040
  have p0042 :=
    @g_addceq12 (.cv j) (.cv j) (.cv k) (.cv k)
  have p0043_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objEq j k) (.objEq j k)) (.classEq (syn_cplc (.cv j) (.cv j)) (syn_cplc (.cv k) (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cplc syn_wrex syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0042
  have p0043 :=
    @g_anidms (.objEq j k) (.classEq (syn_cplc (.cv j) (.cv j)) (syn_cplc (.cv k) (.cv k))) p0043_e00_recanon
  have p0044 :=
    @g_neeq1d (.objEq j k) (syn_cplc (.cv j) (.cv j)) (syn_cplc (.cv k) (.cv k)) (syn_c0) p0043
  have p0045 :=
    @g_neeq1d (.objEq j k) (syn_cplc (.cv j) (.cv j)) (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) p0043
  have p0046 :=
    @g_imbi2d (.objEq j k) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0045
  have p0047 :=
    @g_ralbidv (.objEq j k) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) n (syn_cnnc) dv_cache_0011 p0046
  have p0048 :=
    @g_imbi12d (.objEq j k) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) p0044 p0047
  have p0049 :=
    @g_n_0cnsuc (syn_cplc (.cv n) (.cv n))
  have p0050 :=
    @g_necomi (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0c) p0049
  have p0051 :=
    @g_a1i (syn_wne (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0050
  have p0052 :=
    @g_rgenw (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) n (syn_cnnc) p0051
  have p0053 :=
    @g_a1i (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) (syn_wne (syn_c0c) (syn_c0)) p0052
  have p0054 :=
    @g_addcass (syn_cplc (.cv m) (.cv m)) (syn_c1c) (syn_c1c)
  have p0055 :=
    @g_neeq1i (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_c0) p0054
  have p0056 :=
    @g_addcnnul (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_c1c) (syn_c1c))
  have p0057 :=
    @g_simpld (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_c0)) (syn_wne (syn_cplc (syn_c1c) (syn_c1c)) (syn_c0)) p0056
  have p0058 :=
    @g_sylbi (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_c0)) p0055 p0057
  have p0059 :=
    @g_adantl (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_c0)) (.classMem (.cv m) (syn_cnnc)) p0058
  have p0060 :=
    @g_simprl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))
  have p0061 :=
    @g_nnc0suc q (.cv n) dv_cache_0012
  have p0062 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (.classMem (.cv n) (syn_cnnc)) (syn_wo (.classEq (.cv n) (syn_c0c)) (syn_wrex q (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c))))) p0060 p0061
  have p0063 :=
    @g_n_0cnsuc (syn_cplc (.cv m) (.cv m))
  have p0064 :=
    @g_addceq12 (.cv n) (.cv n) (syn_c0c) (syn_c0c)
  have p0065 :=
    @g_anidms (.classEq (.cv n) (syn_c0c)) (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c0c) (syn_c0c))) p0064
  have p0066 :=
    @g_syl6eq (.classEq (.cv n) (syn_c0c)) (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c) p0065 p0008
  have p0067 :=
    @g_neeq2d (.classEq (.cv n) (syn_c0c)) (syn_cplc (.cv n) (.cv n)) (syn_c0c) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) p0066
  have p0068 :=
    @g_mpbiri (.classEq (.cv n) (syn_c0c)) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c0c)) p0063 p0067
  have p0069 :=
    @g_a1i (.imp (.classEq (.cv n) (syn_c0c)) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) p0068
  have p0070 :=
    @g_simpr (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc))
  have p0071 :=
    @g_adantl (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc))) (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) p0070
  have p0072 :=
    @g_addceq12 (.cv p) (.cv p) (.cv q) (.cv q)
  have p0073_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objEq p q) (.objEq p q)) (.classEq (syn_cplc (.cv p) (.cv p)) (syn_cplc (.cv q) (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cplc syn_wrex syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0072
  have p0073 :=
    @g_anidms (.objEq p q) (.classEq (syn_cplc (.cv p) (.cv p)) (syn_cplc (.cv q) (.cv q))) p0073_e00_recanon
  have p0074 :=
    @g_addceq1d (.objEq p q) (syn_cplc (.cv p) (.cv p)) (syn_cplc (.cv q) (.cv q)) (syn_c1c) p0073
  have p0075 :=
    @g_neeq1d (.objEq p q) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0) p0074
  have p0076 :=
    @g_neeq2d (.objEq p q) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_cplc (.cv m) (.cv m)) p0074
  have p0077 :=
    @g_imbi12d (.objEq p q) (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c))) p0075 p0076
  have p0078_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv p) (.cv q)) (syn_wb (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_cplc syn_wrex syn_wex syn_wa syn_c1c syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0077
  have p0078 :=
    @g_rspcv (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)))) p (.cv q) (syn_cnnc) dv_cache_0013 dv_cache_0007 dv_cache_0014 p0078_e00_recanon
  have p0079 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (.classMem (.cv q) (syn_cnnc)) (.imp (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c))))) p0071 p0078
  have p0080 :=
    @g_addc4 (.cv q) (syn_c1c) (.cv q) (syn_c1c)
  have p0081 :=
    @g_addceq1i (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_c1c) p0080
  have p0082 :=
    @g_addc32 (syn_cplc (.cv q) (.cv q)) (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)
  have p0083 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_cplc (syn_c1c) (syn_c1c))) p0081 p0082
  have p0084 :=
    @g_neeq1i (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_c0) p0083
  have p0085 :=
    @g_addcnnul (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_cplc (syn_c1c) (syn_c1c))
  have p0086 :=
    @g_simpld (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_c1c) (syn_c1c)) (syn_c0)) p0085
  have p0087 :=
    @g_sylbi (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) p0084 p0086
  have p0088 :=
    @g_adantr (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)) p0087
  have p0089 :=
    @g_adantl (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc))) (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) p0088
  have p0090 :=
    @g_addc32 (.cv q) (.cv q) (syn_c1c)
  have p0091 :=
    @g_addceq1i (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (.cv q)) (syn_c1c) p0090
  have p0092 :=
    @g_addcass (syn_cplc (.cv q) (syn_c1c)) (.cv q) (syn_c1c)
  have p0093 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (.cv q)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) p0091 p0092
  have p0094 :=
    @g_eqeq2i (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) p0093
  have p0095 :=
    @g_simplll (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c)))
  have p0096 :=
    @g_nncaddccl (.cv m) (.cv m)
  have p0097 :=
    @g_anidms (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (.cv m)) (syn_cnnc)) p0096
  have p0098 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c)))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (.cv m)) (syn_cnnc)) p0095 p0097
  have p0099 :=
    @g_simplrr (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c)))
  have p0100 :=
    @g_nncaddccl (.cv q) (.cv q)
  have p0101 :=
    @g_anidms (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cplc (.cv q) (.cv q)) (syn_cnnc)) p0100
  have p0102 :=
    @g_peano2 (syn_cplc (.cv q) (.cv q))
  have p0103 :=
    @g_n_3syl (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c)))) (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cplc (.cv q) (.cv q)) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_cnnc)) p0099 p0101 p0102
  have p0104 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c)))
  have p0105 :=
    @g_simpllr (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c)))
  have p0106 :=
    @g_addcnnul (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)
  have p0107 :=
    @g_simpld (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c0)) (syn_wne (syn_c1c) (syn_c0)) p0106
  have p0108 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c)))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c0)) p0105 p0107
  have p0109 :=
    @g_prepeano4 (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c))
  have p0110 :=
    @g_syl22anc (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c)))) (.classMem (syn_cplc (.cv m) (.cv m)) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c))) p0098 p0103 p0104 p0108 p0109
  have p0111 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c))) (.classEq (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c))) p0110
  have p0112 :=
    @g_syl5bir (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c1c))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (.classEq (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c))) p0094 p0111
  have p0113 :=
    @g_necon3d (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) p0112
  have p0114 :=
    @g_embantd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))) p0089 p0113
  have p0115 :=
    @g_syld (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv q) (.cv q)) (syn_c1c)))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))) p0079 p0114
  have p0116 :=
    @g_expr (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.classMem (.cv q) (syn_cnnc)) (.imp (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))))) p0115
  have p0117 :=
    @g_com23 (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0))) (.classMem (.cv q) (syn_cnnc)) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))) p0116
  have p0118 :=
    @g_ex (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.imp (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (.imp (.classMem (.cv q) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))))) p0117
  have p0119 :=
    @g_com23 (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (.imp (.classMem (.cv q) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))))) p0118
  have p0120 :=
    @g_imp31 (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (.imp (.classMem (.cv q) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))))) p0119
  have p0121 :=
    @g_com12 (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0))) (.classMem (.cv q) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))) p0120
  have p0122 :=
    @g_addceq12 (.cv n) (.cv n) (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))
  have p0123 :=
    @g_anidms (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c))) (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))) p0122
  have p0124 :=
    @g_addceq1d (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c))) (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c) p0123
  have p0125 :=
    @g_neeq1d (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c))) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0) p0124
  have p0126 :=
    @g_anbi2d (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0)) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) p0125
  have p0127 :=
    @g_neeq2d (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c))) (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) p0123
  have p0128 :=
    @g_imbi12d (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c))) (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))) p0126 p0127
  have p0129 :=
    @g_syl5ibrcom (.classMem (.cv q) (syn_cnnc)) (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n)))) (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c))) (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))))) p0121 p0128
  have p0130 :=
    @g_rexlimiv (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c))) (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n)))) q (syn_cnnc) dv_cache_0015 p0129
  have p0131 :=
    @g_com12 (syn_wrex q (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n))) p0130
  have p0132 :=
    @g_adantrl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.imp (syn_wrex q (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c)))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) p0131
  have p0133 :=
    @g_jaod (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (.classEq (.cv n) (syn_c0c)) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n))) (syn_wrex q (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c)))) p0069 p0132
  have p0134 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (syn_wo (.classEq (.cv n) (syn_c0c)) (syn_wrex q (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv q) (syn_c1c))))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n))) p0062 p0133
  have p0135 :=
    @g_simplll (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))
  have p0136 :=
    @g_adantr (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) p0135
  have p0137 :=
    @g_peano2 (syn_cplc (.cv m) (.cv m))
  have p0138 :=
    @g_n_3syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (.cv m)) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cnnc)) p0136 p0097 p0137
  have p0139 :=
    @g_simplrl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
  have p0140 :=
    @g_nncaddccl (.cv n) (.cv n)
  have p0141 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0140
  have p0142 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0139 p0141
  have p0143 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
  have p0144 :=
    @g_simpllr (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))
  have p0145 :=
    @g_adantr (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) p0144
  have p0146 :=
    @g_prepeano4 (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n))
  have p0147 :=
    @g_syl22anc (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.classMem (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n))) p0138 p0142 p0143 p0145 p0146
  have p0148 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n))) p0147
  have p0149 :=
    @g_necon3d (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n)) p0148
  have p0150 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (syn_wne (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_cplc (.cv n) (.cv n))) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) p0134 p0149
  have p0151 :=
    @g_expr (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) p0150
  have p0152 :=
    @g_ralrimiva (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) n (syn_cnnc) dv_cache_0016 p0151
  have p0153 :=
    @g_ex (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) p0152
  have p0154 :=
    @g_embantd (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0))) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_c0)) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c))))) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) p0059 p0153
  have p0155 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (.imp (.imp (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_c0)) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))))) p0154
  have p0156 :=
    @g_com23 (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (.imp (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_c0)) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) p0155
  have p0157_e04_recanon : Nominal.NPrf (.imp (.classEq (.cv j) (.cv k)) (syn_wb (.imp (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))))) (.imp (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_cplc syn_wrex syn_wex syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_wral syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0048
  have p0157 :=
    @g_finds (.imp (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))))) (.imp (syn_wne (syn_c0c) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))))) (.imp (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_c0)) (syn_wral p (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (syn_c1c)))))) (.imp (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))))) (.imp (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))))) j m (.cv k) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 p0005 p0014 p0029 p0041 p0157_e04_recanon p0053 p0156
  have p0158 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))))
  have p0159 :=
    @g_imbi2i (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.neg (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0158
  have p0160 :=
    @g_con2b (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
  have p0161 :=
    @g_bitri (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (.neg (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) (.imp (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.neg (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) p0159 p0160
  have p0162 :=
    @g_imnan (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))
  have p0163 :=
    @g_bitri (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.imp (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.neg (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (.neg (syn_wa (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) p0161 p0162
  have p0164 :=
    @g_ralbii (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.neg (syn_wa (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) n (syn_cnnc) p0163
  have p0165 :=
    @g_ralnex (syn_wa (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) n (syn_cnnc)
  have p0166 :=
    @g_bitri (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) (syn_wral n (syn_cnnc) (.neg (syn_wa (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))) (.neg (syn_wrex n (syn_cnnc) (syn_wa (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))) p0164 p0165
  have p0167 :=
    @g_syl6ib (.classMem (.cv k) (syn_cnnc)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)) (syn_wral n (syn_cnnc) (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) (.neg (syn_wrex n (syn_cnnc) (syn_wa (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))) p0157 p0166
  have p0168 :=
    @g_eqeq1 (.cv x) (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0169 :=
    @g_anbi1d (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0168
  have p0170 :=
    @g_rexbidv (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) (syn_wa (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) n (syn_cnnc) dv_cache_0024 p0169
  have p0171 :=
    @g_notbid (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) p0170
  have p0172 :=
    @g_imbi2d (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (.neg (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))) (.neg (syn_wrex n (syn_cnnc) (syn_wa (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)) p0171
  have p0173 :=
    @g_syl5ibrcom (.classMem (.cv k) (syn_cnnc)) (.imp (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)) (.neg (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))) (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (.imp (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)) (.neg (syn_wrex n (syn_cnnc) (syn_wa (.classEq (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))) p0167 p0172
  have p0174 :=
    @g_imp3a (.classMem (.cv k) (syn_cnnc)) (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)) (.neg (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))) p0173
  have p0175 :=
    @g_rexlimiv (syn_wa (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0))) (.neg (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))) k (syn_cnnc) dv_cache_0025 p0174
  have p0176 :=
    @g_imnan (syn_wrex k (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))
  have p0177 :=
    @g_mpbi (.imp (syn_wrex k (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)))) (.neg (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))) (.neg (syn_wa (syn_wrex k (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))) p0175 p0176
  have p0178 :=
    @g_abf (syn_wa (syn_wrex k (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))) x p0177
  have p0179 :=
    @g_eqtri (syn_cin (syn_cevenfin) (syn_coddfin)) (.cab x (syn_wa (syn_wrex k (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv k) (.cv k))) (syn_wne (syn_cplc (.cv k) (.cv k)) (syn_c0)))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))) (syn_c0) p0004 p0178
  exact p0179

#print axioms g_evenodddisj

end NFChoice.DirectNominalPrf.WPPReplay
