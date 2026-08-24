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
import NominalWPPReplayChunk015Compact001Part028

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

noncomputable def g_lnsifnimageexactg
    (R : Class) :
    Nominal.NPrf (.imp (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classEq (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (syn_csi R))) := by
  let proofSupport : Finset Var := R.fv
  let c : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  let y : Var := freshVar proofSupport 4
  let a : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (h)
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact fresh_s (h)
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (h)
  have fresh_c_ne_s : c ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_c : s ≠ c :=
    Ne.symm fresh_c_ne_s
  have fresh_c_ne_p : c ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_c : p ≠ c :=
    Ne.symm fresh_c_ne_p
  have fresh_c_ne_x : c ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_c : x ≠ c :=
    Ne.symm fresh_c_ne_x
  have fresh_c_ne_y : c ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_y_ne_c : y ≠ c :=
    Ne.symm fresh_c_ne_y
  have fresh_c_ne_a : c ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_a_ne_c : a ≠ c :=
    Ne.symm fresh_c_ne_a
  have fresh_c_ne_b : c ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_b_ne_c : b ≠ c :=
    Ne.symm fresh_c_ne_b
  have fresh_s_ne_p : s ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_s : p ≠ s :=
    Ne.symm fresh_s_ne_p
  have fresh_s_ne_x : s ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_s : x ≠ s :=
    Ne.symm fresh_s_ne_x
  have fresh_s_ne_y : s ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_s : y ≠ s :=
    Ne.symm fresh_s_ne_y
  have fresh_s_ne_a : s ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_a_ne_s : a ≠ s :=
    Ne.symm fresh_s_ne_a
  have fresh_s_ne_b : s ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_b_ne_s : b ≠ s :=
    Ne.symm fresh_s_ne_b
  have fresh_p_ne_x : p ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_ne_y : p ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_y_ne_p : y ≠ p :=
    Ne.symm fresh_p_ne_y
  have fresh_p_ne_a : p ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_a_ne_p : a ≠ p :=
    Ne.symm fresh_p_ne_a
  have fresh_p_ne_b : p ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_b_ne_p : b ≠ p :=
    Ne.symm fresh_p_ne_b
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : s ∉ ((Class.cv c)).fv := by
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : s ∉ ((syn_cpw1 R)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : s ∉ ((syn_clnpairraisefn)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((Class.cv s)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : y ∉ ((Wff.imp (.classEq (.cv s) (syn_csn (.cv p))) (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_s, fresh_y_ne_p, fresh_y_ne_c, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Wff.imp (.classEq (.cv s) (syn_csn (.cv p))) (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_s, fresh_x_ne_p, fresh_x_ne_c, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : p ∉ ((Wff.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_s, fresh_p_ne_c, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : s ∉ ((Wff.classMem (.cv c) (syn_csi R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_c, fresh_s_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : s ∉ ((syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : c ∉ ((syn_cima (syn_clnpairraisefn) (syn_cpw1 R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : c ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : c ∉ ((syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : y ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : x ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : y ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : y ∉ ((syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : x ∉ ((syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : a ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : b ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : a ∉ ((syn_cima (syn_clnpairraisefn) (syn_cpw1 R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : b ∉ ((syn_cima (syn_clnpairraisefn) (syn_cpw1 R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    @g_lnpairraisefnfn
  have p0001 :=
    @g_fnfun (syn_cvv) (syn_clnpairraisefn)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_fvelima s (.cv c) (syn_cpw1 R) (syn_clnpairraisefn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_mpan (syn_wfun (syn_clnpairraisefn)) (.classMem (.cv c) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) (syn_wrex s (syn_cpw1 R) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))) p0002 p0003
  have p0005 :=
    @g_a1i (.imp (.classMem (.cv c) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) (syn_wrex s (syn_cpw1 R) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0004
  have p0006 :=
    @g_elpw1 p (.cv s) R dv_cache_0004 dv_cache_0005
  have p0007 :=
    @g_a1i (syn_wb (.classMem (.cv s) (syn_cpw1 R)) (syn_wrex p R (.classEq (.cv s) (syn_csn (.cv p))))) (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0006
  have p0008 :=
    @g_id (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
  have p0009 :=
    @g_sselda (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) R (syn_cxp (syn_cvv) (syn_cvv)) (.cv p) p0008
  have p0010 :=
    @g_elxp x y (.cv p) (syn_cvv) (syn_cvv) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0011 :=
    @g_sylib (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (.classMem (.cv p) (syn_cxp (syn_cvv) (syn_cvv))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))) p0009 p0010
  have p0012 :=
    @g_simpr (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
  have p0013 :=
    @g_n_3simpb (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))) (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))) p0012 p0013
  have p0015 :=
    @g_simpr (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) p0014 p0015
  have p0017 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c) p0016
  have p0018 :=
    @g_simpr (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
  have p0019 :=
    @g_n_3simpa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))) (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p)))) p0018 p0019
  have p0021 :=
    @g_simpr (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p)))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p)))) (.classEq (.cv s) (syn_csn (.cv p))) p0020 p0021
  have p0023 :=
    @g_simpr (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
  have p0024 :=
    @g_n_3simpa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))) (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p)))) p0023 p0024
  have p0026 :=
    @g_simpl (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p)))
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p)))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) p0025 p0026
  have p0028 :=
    @g_simpl (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0027 p0028
  have p0030 :=
    @g_sneqd (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (.cv p) (syn_cop (.cv x) (.cv y)) p0029
  have p0031 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (.cv s) (syn_csn (.cv p)) (syn_csn (syn_cop (.cv x) (.cv y))) p0022 p0030
  have p0032 :=
    @g_fveq2d (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (.cv s) (syn_csn (syn_cop (.cv x) (.cv y))) (syn_clnpairraisefn) p0031
  have p0033 :=
    @g_vex x
  have p0034 :=
    @g_vex y
  have p0035 :=
    @g_lnpairraisefnval (.cv x) (.cv y) p0033 p0034
  have p0036 :=
    @g_a1i (.classEq (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))) (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) p0035
  have p0037 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_cfv (syn_clnpairraisefn) (.cv s)) (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) p0032 p0036
  have p0038 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (.cv c) (syn_cfv (syn_clnpairraisefn) (.cv s)) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) p0017 p0037
  have p0039 :=
    @g_simpr (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
  have p0040 :=
    @g_n_3simpa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))) (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p)))) p0039 p0040
  have p0042 :=
    @g_simpl (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p)))
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p)))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) p0041 p0042
  have p0044 :=
    @g_simpl (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0043 p0044
  have p0046 :=
    @g_simpl (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
  have p0047 :=
    @g_simpr (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)
  have p0048 :=
    @g_syl (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (.classMem (.cv p) R) p0046 p0047
  have p0049 :=
    @g_eqeltrrd (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (.cv p) (syn_cop (.cv x) (.cv y)) R p0045 p0048
  have p0050 :=
    @g_vex x
  have p0051 :=
    @g_vex y
  have p0052 :=
    @g_opsnelsi (.cv x) (.cv y) R p0050 p0051
  have p0053 :=
    @g_sylibr (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (.classMem (syn_cop (.cv x) (.cv y)) R) (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) (syn_csi R)) p0049 p0052
  have p0054 :=
    @g_eqeltrd (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))) (.cv c) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) (syn_csi R) p0038 p0053
  have p0055 :=
    @g_ex (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))) (.classMem (.cv c) (syn_csi R)) p0054
  have p0056 :=
    @g_n_3expd (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq (.cv s) (syn_csn (.cv p))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R)) p0055
  have p0057 :=
    @g_exlimdv (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.imp (.classEq (.cv s) (syn_csn (.cv p))) (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R)))) y dv_cache_0011 dv_cache_0012 p0056
  have p0058 :=
    @g_exlimdv (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_wex y (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) (.imp (.classEq (.cv s) (syn_csn (.cv p))) (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R)))) x dv_cache_0013 dv_cache_0014 p0057
  have p0059 :=
    @g_mpd (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))) (.imp (.classEq (.cv s) (syn_csn (.cv p))) (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R)))) p0011 p0058
  have p0060 :=
    @g_ex (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R) (.imp (.classEq (.cv s) (syn_csn (.cv p))) (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R)))) p0059
  have p0061 :=
    @g_rexlimdv (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classEq (.cv s) (syn_csn (.cv p))) (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R))) p R dv_cache_0015 dv_cache_0016 p0060
  have p0062 :=
    @g_sylbid (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv s) (syn_cpw1 R)) (syn_wrex p R (.classEq (.cv s) (syn_csn (.cv p)))) (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R))) p0007 p0061
  have p0063 :=
    @g_rexlimdv (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) (.classMem (.cv c) (syn_csi R)) s (syn_cpw1 R) dv_cache_0017 dv_cache_0018 p0062
  have p0064 :=
    @g_syld (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv c) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) (syn_wrex s (syn_cpw1 R) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))) (.classMem (.cv c) (syn_csi R)) p0005 p0063
  have p0065 :=
    @g_ssrdv (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) c (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (syn_csi R) dv_cache_0019 dv_cache_0020 dv_cache_0021 p0064
  have p0066 :=
    @g_id (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R))
  have p0067 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) (syn_csi R) (.cv b))))
  have p0068 :=
    @g_sylibr (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R)) (syn_wbr (.cv a) (syn_csi R) (.cv b)) p0066 p0067
  have p0069 :=
    @g_brsi x y (.cv a) (.cv b) R dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0010
  have p0070 :=
    @g_n_3simpa (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0071 :=
    @g_simpl (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
  have p0072 :=
    @g_syl (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))) (.classEq (.cv a) (syn_csn (.cv x))) p0070 p0071
  have p0073 :=
    @g_n_3simpa (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0074 :=
    @g_simpr (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
  have p0075 :=
    @g_syl (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))) (.classEq (.cv b) (syn_csn (.cv y))) p0073 p0074
  have p0076 :=
    @g_opeq12d (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (.cv a) (syn_csn (.cv x)) (.cv b) (syn_csn (.cv y)) p0072 p0075
  have p0077 :=
    @g_vex x
  have p0078 :=
    @g_vex y
  have p0079 :=
    @g_lnpairraisefnval (.cv x) (.cv y) p0077 p0078
  have p0080 :=
    @g_a1i (.classEq (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))) (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) p0079
  have p0081 :=
    @g_eqtr4d (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_cop (.cv a) (.cv b)) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y)))) p0076 p0080
  have p0082 :=
    @g_n_3simpb (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0083 :=
    @g_simpr (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv x) R (.cv y))
  have p0084 :=
    @g_syl (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv x) R (.cv y))) (syn_wbr (.cv x) R (.cv y)) p0082 p0083
  have p0085 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) R (.cv y))))
  have p0086 :=
    @g_sylib (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wbr (.cv x) R (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) R) p0084 p0085
  have p0087 :=
    @g_snelpw1 (syn_cop (.cv x) (.cv y)) R
  have p0088 :=
    @g_sylibr (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (.classMem (syn_cop (.cv x) (.cv y)) R) (.classMem (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cpw1 R)) p0086 p0087
  have p0089 :=
    @g_lnpairraisefnfn
  have p0090 :=
    @g_fnfun (syn_cvv) (syn_clnpairraisefn)
  have p0091 :=
    Nominal.mp p0089 p0090
  have p0092 :=
    @g_snex (syn_cop (.cv x) (.cv y))
  have p0093 :=
    @g_lnpairraisefnfn
  have p0094 :=
    @g_fndm (syn_cvv) (syn_clnpairraisefn)
  have p0095 :=
    Nominal.mp p0093 p0094
  have p0096 :=
    @g_eleqtrri (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cvv) (syn_cdm (syn_clnpairraisefn)) p0092 p0095
  have p0097 :=
    @g_pm3_2i (syn_wfun (syn_clnpairraisefn)) (.classMem (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cdm (syn_clnpairraisefn))) p0091 p0096
  have p0098 :=
    @g_funfvima (syn_cpw1 R) (syn_csn (syn_cop (.cv x) (.cv y))) (syn_clnpairraisefn)
  have p0099 :=
    Nominal.mp p0097 p0098
  have p0100 :=
    @g_syl (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (.classMem (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cpw1 R)) (.classMem (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) p0088 p0099
  have p0101 :=
    @g_eqeltrd (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_cop (.cv a) (.cv b)) (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) p0081 p0100
  have p0102 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b))))
  have p0103 :=
    @g_sylibr (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) p0101 p0102
  have p0104 :=
    @g_exlimiv (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) y dv_cache_0028 p0103
  have p0105 :=
    @g_exlimiv (syn_wex y (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))) (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) x dv_cache_0029 p0104
  have p0106 :=
    @g_sylbi (syn_wbr (.cv a) (syn_csi R) (.cv b)) (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))))) (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) p0069 p0105
  have p0107 :=
    @g_syl (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R)) (syn_wbr (.cv a) (syn_csi R) (.cv b)) (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) p0068 p0106
  have p0108 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b))))
  have p0109 :=
    @g_biimpi (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) p0108
  have p0110 :=
    @g_syl (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R)) (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) p0107 p0109
  have p0111 :=
    Nominal.gen p0110 b
  have p0112 :=
    Nominal.gen p0111 a
  have p0113 :=
    @g_ssrel a b (syn_csi R) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
  have p0114 :=
    @g_mpbir (syn_wss (syn_csi R) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) (.all a (.all b (.imp (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))))) p0112 p0113
  have p0115 :=
    @g_a1i (syn_wss (syn_csi R) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0114
  have p0116 :=
    @g_eqssd (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (syn_csi R) p0065 p0115
  exact p0116

#print axioms g_lnsifnimageexactg

end NFChoice.DirectNominalPrf.WPPReplay
