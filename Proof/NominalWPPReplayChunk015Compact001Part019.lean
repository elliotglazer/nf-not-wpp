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
import NominalWPPReplayChunk015Compact001Part018

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

noncomputable def g_hnqincfun
    (A : Class) (D : Class) (hyp_hnqincfun_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnqincfun_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnqincfun_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wfun (syn_chnqinc D A)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
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
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_p : y ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_y_ne_q : y ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_z_ne_p : z ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have fresh_z_ne_q : z ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0005 : q ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0009 : q ∉ ((Wff.classEq (.cv y) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, fresh_q_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, fresh_q_not_A, fresh_q_not_D, fresh_q_ne_z, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((Wff.classEq (.cv y) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_not_A, fresh_p_not_D, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0017 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0018 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_simpl (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))
  have p0001 :=
    @g_brco p (.cv x) (.cv y) (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_sylib (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wex p (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))
  have p0004 :=
    @g_simpr (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))
  have p0005 :=
    @g_brco q (.cv x) (.cv z) (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0006 :=
    @g_sylib (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z)) (syn_wex q (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) p0004 p0005
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wex q (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) p0003 p0006
  have p0008 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
  have p0009 :=
    @g_simpr (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))) p0008 p0009
  have p0011 :=
    @g_simpr (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)) p0010 p0011
  have p0013 :=
    @g_hnqmap1fn A hyp_hnqincfun_3
  have p0014 :=
    @g_fnfun (syn_cpw1 (syn_chwcn A)) (syn_chnqmap1 A)
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_funbrfv (.cv p) (.cv y) (syn_chnqmap1 A)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (.cv y)) p0012 p0017
  have p0019 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_cfv (syn_chnqmap1 A) (.cv p)) (.cv y) p0018
  have p0020 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
  have p0021 :=
    @g_simpr (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))) p0020 p0021
  have p0023 :=
    @g_simpl (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) p0022 p0023
  have p0025 :=
    @g_brcnv (.cv x) (.cv p) (syn_chnqmap1 D)
  have p0026 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x)) p0024 p0025
  have p0027 :=
    @g_hnqmap1fn D hyp_hnqincfun_2
  have p0028 :=
    @g_fnfun (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_funbrfv (.cv p) (.cv x) (syn_chnqmap1 D)
  have p0031 :=
    Nominal.mp p0029 p0030
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x)) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (.cv x)) p0026 p0031
  have p0033 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
  have p0034 :=
    @g_simpl (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) p0033 p0034
  have p0036 :=
    @g_brcnv (.cv x) (.cv q) (syn_chnqmap1 D)
  have p0037 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv x)) p0035 p0036
  have p0038 :=
    @g_hnqmap1fn D hyp_hnqincfun_2
  have p0039 :=
    @g_fnfun (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_funbrfv (.cv q) (.cv x) (syn_chnqmap1 D)
  have p0042 :=
    Nominal.mp p0040 p0041
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv x)) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv q)) (.cv x)) p0037 p0042
  have p0044 :=
    @g_eqtr4d (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_cfv (syn_chnqmap1 D) (.cv p)) (.cv x) (syn_cfv (syn_chnqmap1 D) (.cv q)) p0032 p0043
  have p0045 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
  have p0046 :=
    @g_simpr (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))) p0045 p0046
  have p0048 :=
    @g_simpl (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))
  have p0049 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) p0047 p0048
  have p0050 :=
    @g_brcnv (.cv x) (.cv p) (syn_chnqmap1 D)
  have p0051 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x)) p0049 p0050
  have p0052 :=
    @g_breldm (.cv p) (.cv x) (syn_chnqmap1 D)
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wbr (.cv p) (syn_chnqmap1 D) (.cv x)) (.classMem (.cv p) (syn_cdm (syn_chnqmap1 D))) p0051 p0052
  have p0054 :=
    @g_hnqmap1fn D hyp_hnqincfun_2
  have p0055 :=
    @g_fndm (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_syl6eleq (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (.cv p) (syn_cdm (syn_chnqmap1 D)) (syn_cpw1 (syn_chwcn D)) p0053 p0056
  have p0058 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
  have p0059 :=
    @g_simpl (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) p0058 p0059
  have p0061 :=
    @g_brcnv (.cv x) (.cv q) (syn_chnqmap1 D)
  have p0062 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv x)) p0060 p0061
  have p0063 :=
    @g_breldm (.cv q) (.cv x) (syn_chnqmap1 D)
  have p0064 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wbr (.cv q) (syn_chnqmap1 D) (.cv x)) (.classMem (.cv q) (syn_cdm (syn_chnqmap1 D))) p0062 p0063
  have p0065 :=
    @g_hnqmap1fn D hyp_hnqincfun_2
  have p0066 :=
    @g_fndm (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_syl6eleq (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (.cv q) (syn_cdm (syn_chnqmap1 D)) (syn_cpw1 (syn_chwcn D)) p0064 p0067
  have p0069 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) p0057 p0068
  have p0070 :=
    @g_hnqmap1basecompat A D q p hyp_hnqincfun_1 hyp_hnqincfun_2 hyp_hnqincfun_3
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.imp (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) p0069 p0070
  have p0072 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) p0044 p0071
  have p0073 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (.cv y) (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)) p0019 p0072
  have p0074 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))
  have p0075 :=
    @g_simpr (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))
  have p0076 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)) p0074 p0075
  have p0077 :=
    @g_hnqmap1fn A hyp_hnqincfun_3
  have p0078 :=
    @g_fnfun (syn_cpw1 (syn_chwcn A)) (syn_chnqmap1 A)
  have p0079 :=
    Nominal.mp p0077 p0078
  have p0080 :=
    @g_funbrfv (.cv q) (.cv z) (syn_chnqmap1 A)
  have p0081 :=
    Nominal.mp p0079 p0080
  have p0082 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv q)) (.cv z)) p0076 p0081
  have p0083 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z)))) (.cv y) (syn_cfv (syn_chnqmap1 A) (.cv q)) (.cv z) p0073 p0082
  have p0084 :=
    @g_exlimddv (syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y)))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv q)) (syn_wbr (.cv q) (syn_chnqmap1 A) (.cv z))) (.classEq (.cv y) (.cv z)) q dv_cache_0009 dv_cache_0010 p0007 p0083
  have p0085 :=
    @g_exlimddv (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 D)) (.cv p)) (syn_wbr (.cv p) (syn_chnqmap1 A) (.cv y))) (.classEq (.cv y) (.cv z)) p dv_cache_0011 dv_cache_0012 p0002 p0084
  have p0086 :=
    Nominal.gen p0085 z
  have p0087 :=
    Nominal.gen p0086 y
  have p0088 :=
    Nominal.gen p0087 x
  have p0089 :=
    @g_dffun2 x y z (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0090_e01_recanon : Nominal.NPrf (syn_wb (syn_wfun (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (.classEq (.cv y) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0089
  have p0090 :=
    @g_mpbir (syn_wfun (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (.cv z))) (.classEq (.cv y) (.cv z)))))) p0088 p0090_e01_recanon
  have p0091 :=
    (by simpa [syn_chnqinc] using (Nominal.classEqRefl (syn_chnqinc D A)))
  have p0092 :=
    @g_funeq (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
  have p0093 :=
    Nominal.mp p0091 p0092
  have p0094 :=
    @g_mpbir (syn_wfun (syn_chnqinc D A)) (syn_wfun (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))) p0090 p0093
  exact p0094

noncomputable def g_hnqincdm
    (A : Class) (D : Class) (hyp_hnqincdm_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnqincdm_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnqincdm_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cdm (syn_chnqinc D A)) (syn_chnord D)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  have p0000 :=
    (by simpa [syn_chnqinc] using (Nominal.classEqRefl (syn_chnqinc D A)))
  have p0001 :=
    @g_dmeqi (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) p0000
  have p0002 :=
    @g_hwcnssbase A D hyp_hnqincdm_1
  have p0003 :=
    @g_pw1ss (syn_chwcn D) (syn_chwcn A)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    (by simpa [syn_cdm] using (Nominal.classEqRefl (syn_cdm (syn_chnqmap1 D))))
  have p0006 :=
    @g_eqcomi (syn_cdm (syn_chnqmap1 D)) (syn_crn (syn_ccnv (syn_chnqmap1 D))) p0005
  have p0007 :=
    @g_hnqmap1fn D hyp_hnqincdm_2
  have p0008 :=
    @g_fndm (syn_cpw1 (syn_chwcn D)) (syn_chnqmap1 D)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_eqtri (syn_crn (syn_ccnv (syn_chnqmap1 D))) (syn_cdm (syn_chnqmap1 D)) (syn_cpw1 (syn_chwcn D)) p0006 p0009
  have p0011 :=
    @g_hnqmap1fn A hyp_hnqincdm_3
  have p0012 :=
    @g_fndm (syn_cpw1 (syn_chwcn A)) (syn_chnqmap1 A)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_n_3sstr4i (syn_cpw1 (syn_chwcn D)) (syn_cpw1 (syn_chwcn A)) (syn_crn (syn_ccnv (syn_chnqmap1 D))) (syn_cdm (syn_chnqmap1 A)) p0004 p0010 p0013
  have p0015 :=
    @g_dmcosseq (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_dfrn4 (syn_chnqmap1 D)
  have p0018 :=
    @g_eqtr4i (syn_cdm (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))) (syn_cdm (syn_ccnv (syn_chnqmap1 D))) (syn_crn (syn_chnqmap1 D)) p0016 p0017
  have p0019 :=
    @g_hnqmap1rn D hyp_hnqincdm_2
  have p0020 :=
    @g_eqtri (syn_cdm (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))) (syn_crn (syn_chnqmap1 D)) (syn_chnord D) p0018 p0019
  have p0021 :=
    @g_eqtri (syn_cdm (syn_chnqinc D A)) (syn_cdm (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))) (syn_chnord D) p0001 p0020
  exact p0021

noncomputable def g_hnqincfn
    (A : Class) (D : Class) (hyp_hnqincfn_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnqincfn_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnqincfn_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_chnqinc D A) (syn_chnord D)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  have p0000 :=
    @g_hnqincfun A D hyp_hnqincfn_1 hyp_hnqincfn_2 hyp_hnqincfn_3
  have p0001 :=
    @g_hnqincdm A D hyp_hnqincfn_1 hyp_hnqincfn_2 hyp_hnqincfn_3
  have p0002 :=
    @g_pm3_2i (syn_wfun (syn_chnqinc D A)) (.classEq (syn_cdm (syn_chnqinc D A)) (syn_chnord D)) p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_chnqinc D A) (syn_chnord D))))
  have p0004 :=
    @g_mpbir (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (syn_wa (syn_wfun (syn_chnqinc D A)) (.classEq (syn_cdm (syn_chnqinc D A)) (syn_chnord D))) p0002 p0003
  exact p0004

noncomputable def g_hnqincf
    (A : Class) (D : Class) (hyp_hnqincf_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnqincf_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnqincf_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  have p0000 :=
    @g_hnqincfn A D hyp_hnqincf_1 hyp_hnqincf_2 hyp_hnqincf_3
  have p0001 :=
    @g_rncoss (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))
  have p0002 :=
    (by simpa [syn_chnqinc] using (Nominal.classEqRefl (syn_chnqinc D A)))
  have p0003 :=
    @g_rneqi (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) p0002
  have p0004 :=
    @g_hnqmap1rn A hyp_hnqincf_3
  have p0005 :=
    @g_eqcomi (syn_crn (syn_chnqmap1 A)) (syn_chnord A) p0004
  have p0006 :=
    @g_n_3sstr4i (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))) (syn_crn (syn_chnqmap1 A)) (syn_crn (syn_chnqinc D A)) (syn_chnord A) p0001 p0003 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (syn_wss (syn_crn (syn_chnqinc D A)) (syn_chnord A)) p0000 p0006
  have p0008 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A))))
  have p0009 :=
    @g_mpbir (syn_wf (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) (syn_wa (syn_wfn (syn_chnqinc D A) (syn_chnord D)) (syn_wss (syn_crn (syn_chnqinc D A)) (syn_chnord A))) p0007 p0008
  exact p0009

#print axioms g_hnqincf

end NFChoice.DirectNominalPrf.WPPReplay
