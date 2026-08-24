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
import NominalWPPReplayChunk013Compact001Part063

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

noncomputable def g_nncdiv3
    (A : Class) (n : Var) (dv_A_n : n ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (syn_wrex n (syn_cnnc) (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))) := by
  let proofSupport : Finset Var := A.fv ∪ ({n} : Finset Var)
  let a : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_a : n ≠ a :=
    Ne.symm fresh_a_ne_n
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (h))
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_m : n ≠ m :=
    Ne.symm fresh_m_ne_n
  have fresh_a_ne_m : a ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_a : m ≠ a :=
    Ne.symm fresh_a_ne_m
  have dv_cache_0001 : a ≠ n := by
    exact (show a ≠ n from (by exact fresh_a_ne_n))
  have dv_cache_0002 : n ∉ ((Wff.classEq (.cv a) (syn_c0c))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((Wff.objEq a m)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((Wff.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.classEq (.cv a) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_a, dv_A_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_cplc (.cv n) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Wff.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((Wff.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((syn_wrex a (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((syn_wrex n (syn_cnnc) (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : m ∉ ((syn_wrex n (syn_cnnc) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_a, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((syn_wrex n (syn_cnnc) (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : a ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show a ≠ m from (by exact fresh_a_ne_m))
  have p0000 :=
    @g_nncdiv3lem2 n a dv_cache_0001
  have p0001 :=
    @g_eqeq1 (.cv a) (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0002 :=
    @g_eqeq1 (.cv a) (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0003 :=
    @g_eqeq1 (.cv a) (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0004 :=
    @g_n_3orbi123d (.classEq (.cv a) (syn_c0c)) (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) p0001 p0002 p0003
  have p0005 :=
    @g_rexbidv (.classEq (.cv a) (syn_c0c)) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) n (syn_cnnc) dv_cache_0002 p0004
  have p0006 :=
    @g_eqeq1 (.cv a) (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0007 :=
    @g_eqeq1 (.cv a) (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0008 :=
    @g_eqeq1 (.cv a) (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0009_e00_recanon : Nominal.NPrf (.imp (.objEq a m) (syn_wb (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0006
  have p0009_e01_recanon : Nominal.NPrf (.imp (.objEq a m) (syn_wb (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0009_e02_recanon : Nominal.NPrf (.imp (.objEq a m) (syn_wb (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c2c syn_cnc syn_cec syn_cima syn_csn syn_cen syn_copab syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_c0 syn_cdif syn_cin syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0008
  have p0009 :=
    @g_n_3orbi123d (.objEq a m) (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) p0009_e00_recanon p0009_e01_recanon p0009_e02_recanon
  have p0010 :=
    @g_rexbidv (.objEq a m) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) n (syn_cnnc) dv_cache_0003 p0009
  have p0011 :=
    @g_eqeq1 (.cv a) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0012 :=
    @g_eqeq1 (.cv a) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0013 :=
    @g_eqeq1 (.cv a) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0014 :=
    @g_n_3orbi123d (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) p0011 p0012 p0013
  have p0015 :=
    @g_rexbidv (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c))) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) n (syn_cnnc) dv_cache_0004 p0014
  have p0016 :=
    @g_eqeq1 (.cv a) A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0017 :=
    @g_eqeq1 (.cv a) A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0018 :=
    @g_eqeq1 (.cv a) A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0019 :=
    @g_n_3orbi123d (.classEq (.cv a) A) (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) p0016 p0017 p0018
  have p0020 :=
    @g_rexbidv (.classEq (.cv a) A) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) n (syn_cnnc) dv_cache_0005 p0019
  have p0021 :=
    @g_peano1
  have p0022 :=
    @g_addcid1 (syn_cplc (syn_c0c) (syn_c0c))
  have p0023 :=
    @g_addcid2 (syn_c0c)
  have p0024 :=
    @g_eqtr2i (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c) p0022 p0023
  have p0025 :=
    @g_n_3mix1 (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c)))
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_addceq12 (.cv n) (.cv n) (syn_c0c) (syn_c0c)
  have p0028 :=
    @g_anidms (.classEq (.cv n) (syn_c0c)) (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c0c) (syn_c0c))) p0027
  have p0029 :=
    @g_id (.classEq (.cv n) (syn_c0c))
  have p0030 :=
    @g_addceq12d (.classEq (.cv n) (syn_c0c)) (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c0c) (syn_c0c)) (.cv n) (syn_c0c) p0028 p0029
  have p0031 :=
    @g_eqeq2d (.classEq (.cv n) (syn_c0c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c0c) p0030
  have p0032 :=
    @g_addceq1d (.classEq (.cv n) (syn_c0c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c) p0030
  have p0033 :=
    @g_eqeq2d (.classEq (.cv n) (syn_c0c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c)) (syn_c0c) p0032
  have p0034 :=
    @g_addceq1d (.classEq (.cv n) (syn_c0c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c) p0030
  have p0035 :=
    @g_eqeq2d (.classEq (.cv n) (syn_c0c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c)) (syn_c0c) p0034
  have p0036 :=
    @g_n_3orbi123d (.classEq (.cv n) (syn_c0c)) (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c))) p0031 p0033 p0035
  have p0037 :=
    @g_rspcev (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c)))) n (syn_c0c) (syn_cnnc) dv_cache_0006 dv_cache_0007 dv_cache_0008 p0036
  have p0038 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c)))) (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) p0021 p0026 p0037
  have p0039 :=
    @g_addceq1 (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)
  have p0040 :=
    @g_reximi (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) n (syn_cnnc) p0039
  have p0041 :=
    @g_a1i (.imp (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (.classMem (.cv m) (syn_cnnc)) p0040
  have p0042 :=
    @g_addceq1 (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_c1c)
  have p0043 :=
    @g_addcass (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c) (syn_c1c)
  have p0044 :=
    @g_n_1p1e2c
  have p0045 :=
    @g_addceq2i (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) p0044
  have p0046 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) p0043 p0045
  have p0047 :=
    @g_syl6eq (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) p0042 p0046
  have p0048 :=
    @g_reximi (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) n (syn_cnnc) p0047
  have p0049 :=
    @g_a1i (.imp (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (.classMem (.cv m) (syn_cnnc)) p0048
  have p0050 :=
    @g_peano2 (.cv n)
  have p0051 :=
    @g_addc32 (syn_cplc (.cv n) (.cv n)) (.cv n) (syn_c2c)
  have p0052 :=
    @g_n_1p1e2c
  have p0053 :=
    @g_addceq2i (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c) (syn_cplc (.cv n) (.cv n)) p0052
  have p0054 :=
    @g_addc4 (.cv n) (.cv n) (syn_c1c) (syn_c1c)
  have p0055 :=
    @g_eqtr3i (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c))) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c2c)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) p0053 p0054
  have p0056 :=
    @g_addceq1i (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c2c)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (.cv n) p0055
  have p0057 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c2c)) (.cv n)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (.cv n)) p0051 p0056
  have p0058 :=
    @g_addceq1i (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (.cv n)) (syn_c1c) p0057
  have p0059 :=
    @g_addcass (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (.cv n) (syn_c1c)
  have p0060 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (.cv n)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c))) p0058 p0059
  have p0061 :=
    @g_addceq12 (.cv a) (.cv a) (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))
  have p0062 :=
    @g_anidms (.classEq (.cv a) (syn_cplc (.cv n) (syn_c1c))) (.classEq (syn_cplc (.cv a) (.cv a)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) p0061
  have p0063 :=
    @g_id (.classEq (.cv a) (syn_cplc (.cv n) (syn_c1c)))
  have p0064 :=
    @g_addceq12d (.classEq (.cv a) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv a) (.cv a)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (.cv a) (syn_cplc (.cv n) (syn_c1c)) p0062 p0063
  have p0065 :=
    @g_eqeq2d (.classEq (.cv a) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) p0064
  have p0066 :=
    @g_rspcev (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))) (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c)))) a (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0065
  have p0067 :=
    @g_sylancl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv n) (syn_c1c)))) (syn_wrex a (syn_cnnc) (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))) p0050 p0060 p0066
  have p0068 :=
    @g_addceq1 (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)
  have p0069 :=
    @g_eqeq1d (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)) p0068
  have p0070 :=
    @g_rexbidv (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))) (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))) a (syn_cnnc) dv_cache_0012 p0069
  have p0071 :=
    @g_syl5ibrcom (.classMem (.cv n) (syn_cnnc)) (syn_wrex a (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_wrex a (syn_cnnc) (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))) p0067 p0070
  have p0072 :=
    @g_rexlimiv (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) (syn_wrex a (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))) n (syn_cnnc) dv_cache_0013 p0071
  have p0073 :=
    @g_addceq12 (.cv a) (.cv a) (.cv n) (.cv n)
  have p0074_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objEq a n) (.objEq a n)) (.classEq (syn_cplc (.cv a) (.cv a)) (syn_cplc (.cv n) (.cv n)))) :=
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
      p0073
  have p0074 :=
    @g_anidms (.objEq a n) (.classEq (syn_cplc (.cv a) (.cv a)) (syn_cplc (.cv n) (.cv n))) p0074_e00_recanon
  have p0075 :=
    @g_id (.objEq a n)
  have p0076_e01_recanon : Nominal.NPrf (.imp (.objEq a n) (.classEq (.cv a) (.cv n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0075
  have p0076 :=
    @g_addceq12d (.objEq a n) (syn_cplc (.cv a) (.cv a)) (syn_cplc (.cv n) (.cv n)) (.cv a) (.cv n) p0074 p0076_e01_recanon
  have p0077 :=
    @g_eqeq2d (.objEq a n) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (.cv m) (syn_c1c)) p0076
  have p0078 :=
    @g_cbvrexv (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) a n (syn_cnnc) dv_cache_0010 dv_cache_0007 dv_cache_0014 dv_cache_0015 p0077
  have p0079 :=
    @g_sylib (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_wrex a (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) p0072 p0078
  have p0080 :=
    @g_a1i (.imp (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))) (.classMem (.cv m) (syn_cnnc)) p0079
  have p0081 :=
    @g_n_3orim123d (.classMem (.cv m) (syn_cnnc)) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) p0041 p0049 p0080
  have p0082 :=
    (by simpa [syn_wb, syn_w3o] using (Nominal.biimpRefl (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))))
  have p0083 :=
    @g_rexbii (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_wo (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) n (syn_cnnc) p0082
  have p0084 :=
    @g_r19_43 (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) n (syn_cnnc)
  have p0085 :=
    @g_orbi1i (syn_wrex n (syn_cnnc) (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (syn_wo (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) p0084
  have p0086 :=
    @g_r19_43 (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) n (syn_cnnc)
  have p0087 :=
    (by simpa [syn_wb, syn_w3o] using (Nominal.biimpRefl (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))))
  have p0088 :=
    @g_n_3bitr4i (syn_wo (syn_wrex n (syn_cnnc) (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wo (syn_wo (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wrex n (syn_cnnc) (syn_wo (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) p0085 p0086 p0087
  have p0089 :=
    @g_bitri (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wrex n (syn_cnnc) (syn_wo (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) p0083 p0088
  have p0090 :=
    (by simpa [syn_wb, syn_w3o] using (Nominal.biimpRefl (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))))
  have p0091 :=
    @g_rexbii (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_wo (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) n (syn_cnnc) p0090
  have p0092 :=
    @g_r19_43 (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) n (syn_cnnc)
  have p0093 :=
    @g_r19_43 (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) n (syn_cnnc)
  have p0094 :=
    @g_orbi1i (syn_wrex n (syn_cnnc) (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (syn_wo (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) p0093
  have p0095 :=
    (by simpa [syn_wb, syn_w3o] using (Nominal.biimpRefl (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))))
  have p0096 :=
    @g_n_3orrot (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
  have p0097 :=
    @g_n_3bitr2i (syn_wo (syn_wrex n (syn_cnnc) (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wo (syn_wo (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))) p0094 p0095 p0096
  have p0098 :=
    @g_bitri (syn_wrex n (syn_cnnc) (syn_wo (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wo (syn_wrex n (syn_cnnc) (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))) p0092 p0097
  have p0099 :=
    @g_bitri (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wrex n (syn_cnnc) (syn_wo (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))) p0091 p0098
  have p0100 :=
    @g_n_3imtr4g (.classMem (.cv m) (syn_cnnc)) (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))) (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) p0081 p0089 p0099
  have p0101 :=
    @g_finds (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) (syn_wrex n (syn_cnnc) (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) a m A dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 p0000 p0005 p0010 p0015 p0020 p0038 p0100
  exact p0101

#print axioms g_nncdiv3

end NFChoice.DirectNominalPrf.WPPReplay
