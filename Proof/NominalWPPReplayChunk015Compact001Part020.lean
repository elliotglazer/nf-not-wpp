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
import NominalWPPReplayChunk015Compact001Part019

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

noncomputable def g_hnqincf1
    (A : Class) (D : Class) (hyp_hnqincf1_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnqincf1_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnqincf1_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf1 (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let q : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_y_ne_p : y ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_y_ne_q : y ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cfv (syn_chnqinc D A) (.cv x))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_not_A, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_chnqmap1 A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_ccnv (syn_chnqmap1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_cfv (syn_chnqinc D A) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, fresh_q_not_A, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_chnqmap1 A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((syn_ccnv (syn_chnqmap1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : q ∉ ((Wff.classEq (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_not_D, fresh_q_ne_y, fresh_q_not_A, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((Wff.classEq (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_not_D, fresh_p_ne_y, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_chnord D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0015 : x ∉ ((syn_chnord D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_chnqinc D A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_chnqinc D A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnqincf A D hyp_hnqincf1_1 hyp_hnqincf1_2 hyp_hnqincf1_3
  have p0001 :=
    @g_simpl (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))
  have p0002 :=
    @g_eqid (syn_cfv (syn_chnqinc D A) (.cv x))
  have p0003 :=
    @g_a1i (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv x))) (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) p0002
  have p0004 :=
    @g_hnqincfn A D hyp_hnqincf1_1 hyp_hnqincf1_2 hyp_hnqincf1_3
  have p0005 :=
    @g_a1i (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) p0004
  have p0006 :=
    @g_simpl (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))
  have p0007 :=
    @g_jca (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (.classMem (.cv x) (syn_chnord D)) p0005 p0006
  have p0008 :=
    @g_fnbrfvb (syn_chnord D) (.cv x) (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_chnqinc D A)
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wa (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (.classMem (.cv x) (syn_chnord D))) (syn_wb (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv x))) (syn_wbr (.cv x) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv x)))) p0007 p0008
  have p0010 :=
    @g_mpbid (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv x))) (syn_wbr (.cv x) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv x))) p0003 p0009
  have p0011 :=
    (by simpa [syn_chnqinc] using (Nominal.classEqRefl (syn_chnqinc D A)))
  have p0012 :=
    @g_breqi (.cv x) (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) p0011
  have p0013 :=
    @g_sylib (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wbr (.cv x) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv x))) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (syn_cfv (syn_chnqinc D A) (.cv x))) p0010 p0012
  have p0014 :=
    @g_brco p (.cv x) (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0015 :=
    @g_sylib (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (syn_cfv (syn_chnqinc D A) (.cv x))) (syn_wex p (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) p0013 p0014
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wex p (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) p0001 p0015
  have p0017 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
  have p0018 :=
    @g_simpl (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))
  have p0019 :=
    @g_eqid (syn_cfv (syn_chnqinc D A) (.cv y))
  have p0020 :=
    @g_a1i (.classEq (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_cfv (syn_chnqinc D A) (.cv y))) (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) p0019
  have p0021 :=
    @g_hnqincfn A D hyp_hnqincf1_1 hyp_hnqincf1_2 hyp_hnqincf1_3
  have p0022 :=
    @g_a1i (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) p0021
  have p0023 :=
    @g_simpr (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))
  have p0024 :=
    @g_jca (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D)) p0022 p0023
  have p0025 :=
    @g_fnbrfvb (syn_chnord D) (.cv y) (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_chnqinc D A)
  have p0026 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wa (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wb (.classEq (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_cfv (syn_chnqinc D A) (.cv y))) (syn_wbr (.cv y) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv y)))) p0024 p0025
  have p0027 :=
    @g_mpbid (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_cfv (syn_chnqinc D A) (.cv y))) (syn_wbr (.cv y) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv y))) p0020 p0026
  have p0028 :=
    (by simpa [syn_chnqinc] using (Nominal.classEqRefl (syn_chnqinc D A)))
  have p0029 :=
    @g_breqi (.cv y) (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) p0028
  have p0030 :=
    @g_sylib (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wbr (.cv y) (syn_chnqinc D A) (syn_cfv (syn_chnqinc D A) (.cv y))) (syn_wbr (.cv y) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (syn_cfv (syn_chnqinc D A) (.cv y))) p0027 p0029
  have p0031 :=
    @g_brco q (.cv y) (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0032 :=
    @g_sylib (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wbr (.cv y) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (syn_cfv (syn_chnqinc D A) (.cv y))) (syn_wex q (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) p0030 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (syn_wex q (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) p0018 p0032
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wex q (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) p0017 p0033
  have p0035 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
  have p0036 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))) p0035 p0036
  have p0038 :=
    @g_simpl (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))
  have p0039 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) p0037 p0038
  have p0040 :=
    @g_brcnv (.cv x) (.cv p) (syn_chnqmap1 D)
  have p0041 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x)) p0039 p0040
  have p0042 :=
    @g_hnqmap1fn D hyp_hnqincf1_2
  have p0043 :=
    @g_fnfun (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_funbrfv (.cv p) (.cv x) (syn_chnqmap1 D)
  have p0046 :=
    Nominal.mp p0044 p0045
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x)) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (.cv x)) p0041 p0046
  have p0048 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_cfv (syn_chnqmap1 D) (.cv p)) (.cv x) p0047
  have p0049 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
  have p0050 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
  have p0051 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))) p0049 p0050
  have p0052 :=
    @g_simpr (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))) p0051 p0052
  have p0054 :=
    @g_hnqmap1fn A hyp_hnqincf1_3
  have p0055 :=
    @g_fnfun (syn_cpw1 (syn_chwcn A)) (syn_chnqmap1 A)
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_funbrfv (.cv p) (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_chnqmap1 A)
  have p0058 :=
    Nominal.mp p0056 p0057
  have p0059 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqinc D A) (.cv x))) p0053 p0058
  have p0060 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
  have p0061 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
  have p0062 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) p0060 p0061
  have p0063 :=
    @g_simpr (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))
  have p0064 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))) p0062 p0063
  have p0065 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)) p0059 p0064
  have p0066 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
  have p0067 :=
    @g_simpr (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))) p0066 p0067
  have p0069 :=
    @g_hnqmap1fn A hyp_hnqincf1_3
  have p0070 :=
    @g_fnfun (syn_cpw1 (syn_chwcn A)) (syn_chnqmap1 A)
  have p0071 :=
    Nominal.mp p0069 p0070
  have p0072 :=
    @g_funbrfv (.cv q) (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_chnqmap1 A)
  have p0073 :=
    Nominal.mp p0071 p0072
  have p0074 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cfv (syn_chnqinc D A) (.cv y))) p0068 p0073
  have p0075 :=
    @g_eqtr4d (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqinc D A) (.cv y)) (syn_cfv (syn_chnqmap1 A) (.cv q)) p0065 p0074
  have p0076 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
  have p0077 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))
  have p0078 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))) p0076 p0077
  have p0079 :=
    @g_simpl (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) p0078 p0079
  have p0081 :=
    @g_brcnv (.cv x) (.cv p) (syn_chnqmap1 D)
  have p0082 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x)) p0080 p0081
  have p0083 :=
    @g_breldm (.cv p) (.cv x) (syn_chnqmap1 D)
  have p0084 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x)) (.classMem (.cv p) (syn_cdm (syn_chnqmap1 D))) p0082 p0083
  have p0085 :=
    @g_hnqmap1fn D hyp_hnqincf1_2
  have p0086 :=
    @g_fndm (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0087 :=
    Nominal.mp p0085 p0086
  have p0088 :=
    @g_syl6eleq (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (.cv p) (syn_cdm (syn_chnqmap1 D)) (syn_cpw1 (syn_chwcn D)) p0084 p0087
  have p0089 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
  have p0090 :=
    @g_simpl (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))
  have p0091 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) p0089 p0090
  have p0092 :=
    @g_brcnv (.cv y) (.cv q) (syn_chnqmap1 D)
  have p0093 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv y)) p0091 p0092
  have p0094 :=
    @g_breldm (.cv q) (.cv y) (syn_chnqmap1 D)
  have p0095 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv y)) (.classMem (.cv q) (syn_cdm (syn_chnqmap1 D))) p0093 p0094
  have p0096 :=
    @g_hnqmap1fn D hyp_hnqincf1_2
  have p0097 :=
    @g_fndm (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0098 :=
    Nominal.mp p0096 p0097
  have p0099 :=
    @g_syl6eleq (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (.cv q) (syn_cdm (syn_chnqmap1 D)) (syn_cpw1 (syn_chwcn D)) p0095 p0098
  have p0100 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) p0088 p0099
  have p0101 :=
    @g_hnqmap1basereflect A D q p hyp_hnqincf1_1 hyp_hnqincf1_2 hyp_hnqincf1_3
  have p0102 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.imp (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) p0100 p0101
  have p0103 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) p0075 p0102
  have p0104 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (.cv x) (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)) p0048 p0103
  have p0105 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))
  have p0106 :=
    @g_simpl (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))
  have p0107 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) p0105 p0106
  have p0108 :=
    @g_brcnv (.cv y) (.cv q) (syn_chnqmap1 D)
  have p0109 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv y)) p0107 p0108
  have p0110 :=
    @g_hnqmap1fn D hyp_hnqincf1_2
  have p0111 :=
    @g_fnfun (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0112 :=
    Nominal.mp p0110 p0111
  have p0113 :=
    @g_funbrfv (.cv q) (.cv y) (syn_chnqmap1 D)
  have p0114 :=
    Nominal.mp p0112 p0113
  have p0115 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv y)) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv q)) (.cv y)) p0109 p0114
  have p0116 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y))))) (.cv x) (syn_cfv (syn_chnqmap1 D) (.cv q)) (.cv y) p0104 p0115
  have p0117 :=
    @g_exlimddv (syn_wa (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x))))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv y)))) (.classEq (.cv x) (.cv y)) q dv_cache_0009 dv_cache_0010 p0034 p0116
  have p0118 :=
    @g_exlimddv (syn_wa (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (syn_cfv (syn_chnqinc D A) (.cv x)))) (.classEq (.cv x) (.cv y)) p dv_cache_0011 dv_cache_0012 p0016 p0117
  have p0119 :=
    @g_ex (syn_wa (.classMem (.cv x) (syn_chnord D)) (.classMem (.cv y) (syn_chnord D))) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))) (.classEq (.cv x) (.cv y)) p0118
  have p0120 :=
    @g_rgen2 (.imp (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))) (.classEq (.cv x) (.cv y))) x y (syn_chnord D) (syn_chnord D) dv_cache_0013 dv_cache_0014 p0119
  have p0121 :=
    @g_pm3_2i (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) (syn_wral x (syn_chnord D) (syn_wral y (syn_chnord D) (.imp (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))) (.classEq (.cv x) (.cv y))))) p0000 p0120
  have p0122 :=
    @g_dff13 x y (syn_chnord D) (syn_chnord A) (syn_chnqinc D A) dv_cache_0015 dv_cache_0013 dv_cache_0016 dv_cache_0017 dv_cache_0014
  have p0123_e01_recanon : Nominal.NPrf (syn_wb (syn_wf1 (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) (syn_wa (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) (syn_wral x (syn_chnord D) (syn_wral y (syn_chnord D) (.imp (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))) (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_chnqinc syn_chnord syn_cqs syn_wrex syn_cec syn_cima syn_csn syn_chwcn syn_chwniso
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0122
  have p0123 :=
    @g_mpbir (syn_wf1 (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) (syn_wa (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) (syn_wral x (syn_chnord D) (syn_wral y (syn_chnord D) (.imp (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (.cv y))) (.classEq (.cv x) (.cv y)))))) p0121 p0123_e01_recanon
  exact p0123

#print axioms g_hnqincf1

end NFChoice.DirectNominalPrf.WPPReplay
