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
import NominalWPPReplayChunk013Compact001Part053

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

noncomputable def g_lenc
    (x : Var) (A : Class) (M : Class) (dv_A_x : x ∉ A.fv) (dv_M_x : x ∉ M.fv) (hyp_lenc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem M (syn_cncs)) (syn_wb (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ M.fv
  let y : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  let q : Var := freshVar proofSupport 2
  let f : Var := freshVar proofSupport 3
  let g : Var := freshVar proofSupport 4
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_f_ne_x : f ≠ x := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_f : x ≠ f :=
    Ne.symm fresh_f_ne_x
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_M : f ∉ M.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_g_ne_x : g ≠ x := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_g : x ≠ g :=
    Ne.symm fresh_g_ne_x
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_M : g ∉ M.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_y_ne_p : y ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_y_ne_q : y ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_y_ne_f : y ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_g_ne_y : g ≠ y :=
    Ne.symm fresh_y_ne_g
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have fresh_p_ne_f : p ≠ f := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_f_ne_p : f ≠ p :=
    Ne.symm fresh_p_ne_f
  have fresh_p_ne_g : p ≠ g := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_g_ne_p : g ≠ p :=
    Ne.symm fresh_p_ne_g
  have fresh_q_ne_f : q ≠ f := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_f_ne_q : f ≠ q :=
    Ne.symm fresh_q_ne_f
  have fresh_q_ne_g : q ≠ g := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_g_ne_q : g ≠ q :=
    Ne.symm fresh_q_ne_g
  have fresh_f_ne_g : f ≠ g := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_g_ne_f : g ≠ f :=
    Ne.symm fresh_f_ne_g
  have dv_cache_0001 : y ∉ (M).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cnc (.cv y))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0006 : f ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : f ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : g ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : g ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : g ∉ ((syn_wf1o (.cv f) (.cv p) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_p, fresh_g_ne_y, fresh_g_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : f ∉ ((syn_wf1o (.cv g) (.cv q) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_q, fresh_f_not_A, fresh_f_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_cima (.cv g) (.cv p))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_g, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_cnc (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_wss (syn_cima (.cv g) (.cv p)) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_g, fresh_x_ne_p, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : f ∉ ((Wff.imp (syn_wss (.cv p) (.cv q)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_p, fresh_f_ne_q, fresh_f_ne_y, fresh_f_ne_x, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : g ∉ ((Wff.imp (syn_wss (.cv p) (.cv q)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_p, fresh_g_ne_q, fresh_g_ne_y, fresh_g_ne_x, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : q ∉ ((syn_cnc (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : q ∉ ((syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, fresh_q_ne_x, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : x ∉ ((syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : y ∉ ((syn_wb (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elncs y M dv_cache_0001
  have p0001 :=
    @g_ncex (.cv y)
  have p0002 :=
    @g_ncex A
  have p0003 :=
    @g_brlec p q (syn_cnc (.cv y)) (syn_cnc A) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0001 p0002
  have p0004 :=
    @g_elnc (.cv p) (.cv y)
  have p0005 :=
    @g_bren (.cv p) (.cv y) f dv_cache_0006 dv_cache_0007
  have p0006 :=
    @g_bitri (.classMem (.cv p) (syn_cnc (.cv y))) (syn_wbr (.cv p) (syn_cen) (.cv y)) (syn_wex f (syn_wf1o (.cv f) (.cv p) (.cv y))) p0004 p0005
  have p0007 :=
    @g_elnc (.cv q) A
  have p0008 :=
    @g_bren (.cv q) A g dv_cache_0008 dv_cache_0009
  have p0009 :=
    @g_bitri (.classMem (.cv q) (syn_cnc A)) (syn_wbr (.cv q) (syn_cen) A) (syn_wex g (syn_wf1o (.cv g) (.cv q) A)) p0007 p0008
  have p0010 :=
    @g_anbi12i (.classMem (.cv p) (syn_cnc (.cv y))) (syn_wex f (syn_wf1o (.cv f) (.cv p) (.cv y))) (.classMem (.cv q) (syn_cnc A)) (syn_wex g (syn_wf1o (.cv g) (.cv q) A)) p0006 p0009
  have p0011 :=
    @g_eeanv (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) f g dv_cache_0010 dv_cache_0011
  have p0012 :=
    @g_bitr4i (syn_wa (.classMem (.cv p) (syn_cnc (.cv y))) (.classMem (.cv q) (syn_cnc A))) (syn_wa (syn_wex f (syn_wf1o (.cv f) (.cv p) (.cv y))) (syn_wex g (syn_wf1o (.cv g) (.cv q) A))) (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)))) p0010 p0011
  have p0013 :=
    @g_f1of1 (.cv q) A (.cv g)
  have p0014 :=
    @g_n_3ad2ant2 (syn_wf1o (.cv g) (.cv q) A) (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1 (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q)) p0013
  have p0015 :=
    @g_simp3 (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q))
  have p0016 :=
    @g_f1ores (.cv q) A (.cv p) (.cv g)
  have p0017 :=
    @g_syl2anc (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q))) (syn_wf1 (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q)) (syn_wf1o (syn_cres (.cv g) (.cv p)) (.cv p) (syn_cima (.cv g) (.cv p))) p0014 p0015 p0016
  have p0018 :=
    @g_f1ocnv (.cv p) (.cv y) (.cv f)
  have p0019 :=
    @g_n_3ad2ant1 (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) (syn_wf1o (syn_ccnv (.cv f)) (.cv y) (.cv p)) (syn_wss (.cv p) (.cv q)) p0018
  have p0020 :=
    @g_f1oco (.cv y) (.cv p) (syn_cima (.cv g) (.cv p)) (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f))
  have p0021 :=
    @g_syl2anc (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q))) (syn_wf1o (syn_cres (.cv g) (.cv p)) (.cv p) (syn_cima (.cv g) (.cv p))) (syn_wf1o (syn_ccnv (.cv f)) (.cv y) (.cv p)) (syn_wf1o (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f))) (.cv y) (syn_cima (.cv g) (.cv p))) p0017 p0019 p0020
  have p0022 :=
    @g_f1ocnv (.cv y) (syn_cima (.cv g) (.cv p)) (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f)))
  have p0023 :=
    @g_vex g
  have p0024 :=
    @g_vex p
  have p0025 :=
    @g_resex (.cv g) (.cv p) p0023 p0024
  have p0026 :=
    @g_vex f
  have p0027 :=
    @g_cnvex (.cv f) p0026
  have p0028 :=
    @g_coex (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f)) p0025 p0027
  have p0029 :=
    @g_cnvex (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f))) p0028
  have p0030 :=
    @g_f1oen (syn_cima (.cv g) (.cv p)) (.cv y) (syn_ccnv (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f)))) p0029
  have p0031 :=
    @g_n_3syl (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q))) (syn_wf1o (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f))) (.cv y) (syn_cima (.cv g) (.cv p))) (syn_wf1o (syn_ccnv (syn_ccom (syn_cres (.cv g) (.cv p)) (syn_ccnv (.cv f)))) (syn_cima (.cv g) (.cv p)) (.cv y)) (syn_wbr (syn_cima (.cv g) (.cv p)) (syn_cen) (.cv y)) p0021 p0022 p0030
  have p0032 :=
    @g_elnc (syn_cima (.cv g) (.cv p)) (.cv y)
  have p0033 :=
    @g_sylibr (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q))) (syn_wbr (syn_cima (.cv g) (.cv p)) (syn_cen) (.cv y)) (.classMem (syn_cima (.cv g) (.cv p)) (syn_cnc (.cv y))) p0031 p0032
  have p0034 :=
    @g_imass2 (.cv p) (.cv q) (.cv g)
  have p0035 :=
    @g_n_3ad2ant3 (syn_wss (.cv p) (.cv q)) (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wss (syn_cima (.cv g) (.cv p)) (syn_cima (.cv g) (.cv q))) (syn_wf1o (.cv g) (.cv q) A) p0034
  have p0036 :=
    @g_f1ofo (.cv q) A (.cv g)
  have p0037 :=
    @g_foima (.cv q) A (.cv g)
  have p0038 :=
    @g_syl (syn_wf1o (.cv g) (.cv q) A) (syn_wfo (.cv g) (.cv q) A) (.classEq (syn_cima (.cv g) (.cv q)) A) p0036 p0037
  have p0039 :=
    @g_n_3ad2ant2 (syn_wf1o (.cv g) (.cv q) A) (syn_wf1o (.cv f) (.cv p) (.cv y)) (.classEq (syn_cima (.cv g) (.cv q)) A) (syn_wss (.cv p) (.cv q)) p0038
  have p0040 :=
    @g_sseqtrd (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q))) (syn_cima (.cv g) (.cv p)) (syn_cima (.cv g) (.cv q)) A p0035 p0039
  have p0041 :=
    @g_sseq1 (.cv x) (syn_cima (.cv g) (.cv p)) A
  have p0042 :=
    @g_rspcev (syn_wss (.cv x) A) (syn_wss (syn_cima (.cv g) (.cv p)) A) x (syn_cima (.cv g) (.cv p)) (syn_cnc (.cv y)) dv_cache_0012 dv_cache_0013 dv_cache_0014 p0041
  have p0043 :=
    @g_syl2anc (syn_w3a (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q))) (.classMem (syn_cima (.cv g) (.cv p)) (syn_cnc (.cv y))) (syn_wss (syn_cima (.cv g) (.cv p)) A) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p0033 p0040 p0042
  have p0044 :=
    @g_n_3expia (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A) (syn_wss (.cv p) (.cv q)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p0043
  have p0045 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)) (.imp (syn_wss (.cv p) (.cv q)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A))) f g dv_cache_0015 dv_cache_0016 p0044
  have p0046 :=
    @g_sylbi (syn_wa (.classMem (.cv p) (syn_cnc (.cv y))) (.classMem (.cv q) (syn_cnc A))) (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) (.cv p) (.cv y)) (syn_wf1o (.cv g) (.cv q) A)))) (.imp (syn_wss (.cv p) (.cv q)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A))) p0012 p0045
  have p0047 :=
    @g_rexlimivv (syn_wss (.cv p) (.cv q)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p q (syn_cnc (.cv y)) (syn_cnc A) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0005 p0046
  have p0048 :=
    @g_sylbi (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A)) (syn_wrex p (syn_cnc (.cv y)) (syn_wrex q (syn_cnc A) (syn_wss (.cv p) (.cv q)))) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p0003 p0047
  have p0049 :=
    @g_vex x
  have p0050 :=
    @g_nclec (.cv x) A p0049 hyp_lenc_1
  have p0051 :=
    @g_eqnc (.cv x) (.cv y) p0049
  have p0052 :=
    @g_elnc (.cv x) (.cv y)
  have p0053 :=
    @g_bitr4i (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y))) (syn_wbr (.cv x) (syn_cen) (.cv y)) (.classMem (.cv x) (syn_cnc (.cv y))) p0051 p0052
  have p0054 :=
    @g_breq1 (syn_cnc (.cv x)) (syn_cnc (.cv y)) (syn_cnc A) (syn_clec)
  have p0055 :=
    @g_sylbir (.classMem (.cv x) (syn_cnc (.cv y))) (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y))) (syn_wb (syn_wbr (syn_cnc (.cv x)) (syn_clec) (syn_cnc A)) (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A))) p0053 p0054
  have p0056 :=
    @g_syl5ib (syn_wss (.cv x) A) (syn_wbr (syn_cnc (.cv x)) (syn_clec) (syn_cnc A)) (.classMem (.cv x) (syn_cnc (.cv y))) (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A)) p0050 p0055
  have p0057 :=
    @g_rexlimiv (syn_wss (.cv x) A) (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A)) x (syn_cnc (.cv y)) dv_cache_0020 p0056
  have p0058 :=
    @g_impbii (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p0048 p0057
  have p0059 :=
    @g_breq1 M (syn_cnc (.cv y)) (syn_cnc A) (syn_clec)
  have p0060 :=
    @g_rexeq (syn_wss (.cv x) A) x M (syn_cnc (.cv y)) dv_cache_0021 dv_cache_0013
  have p0061 :=
    @g_bibi12d (.classEq M (syn_cnc (.cv y))) (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A)) p0059 p0060
  have p0062 :=
    @g_mpbiri (.classEq M (syn_cnc (.cv y))) (syn_wb (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A))) (syn_wb (syn_wbr (syn_cnc (.cv y)) (syn_clec) (syn_cnc A)) (syn_wrex x (syn_cnc (.cv y)) (syn_wss (.cv x) A))) p0058 p0061
  have p0063 :=
    @g_exlimiv (.classEq M (syn_cnc (.cv y))) (syn_wb (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A))) y dv_cache_0022 p0062
  have p0064 :=
    @g_sylbi (.classMem M (syn_cncs)) (syn_wex y (.classEq M (syn_cnc (.cv y)))) (syn_wb (syn_wbr M (syn_clec) (syn_cnc A)) (syn_wrex x M (syn_wss (.cv x) A))) p0000 p0063
  exact p0064

noncomputable def g_tcncg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A)))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_ncelncs A V
  have p0001 :=
    @g_tccl (syn_cnc A)
  have p0002 :=
    @g_syl (.classMem A V) (.classMem (syn_cnc A) (syn_cncs)) (.classMem (syn_ctc (syn_cnc A)) (syn_cncs)) p0000 p0001
  have p0003 :=
    @g_pw1exg A V
  have p0004 :=
    @g_ncelncs (syn_cpw1 A) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem A V) (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem (syn_cnc (syn_cpw1 A)) (syn_cncs)) p0003 p0004
  have p0006 :=
    @g_ncidg A V
  have p0007 :=
    @g_pw1eltc (syn_cnc A) A
  have p0008 :=
    @g_syl2anc (.classMem A V) (.classMem (syn_cnc A) (syn_cncs)) (.classMem A (syn_cnc A)) (.classMem (syn_cpw1 A) (syn_ctc (syn_cnc A))) p0000 p0006 p0007
  have p0009 :=
    @g_ncidg (syn_cpw1 A) (syn_cvv)
  have p0010 :=
    @g_syl (.classMem A V) (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem (syn_cpw1 A) (syn_cnc (syn_cpw1 A))) p0003 p0009
  have p0011 :=
    @g_nceleq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A)) (syn_cpw1 A)
  have p0012 :=
    @g_syl22anc (.classMem A V) (.classMem (syn_ctc (syn_cnc A)) (syn_cncs)) (.classMem (syn_cnc (syn_cpw1 A)) (syn_cncs)) (.classMem (syn_cpw1 A) (syn_ctc (syn_cnc A))) (.classMem (syn_cpw1 A) (syn_cnc (syn_cpw1 A))) (.classEq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A))) p0002 p0005 p0008 p0010 p0011
  exact p0012

noncomputable def g_tcnc
    (A : Class) (hyp_tcnc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_tcncg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_tcnc_1 p0000
  exact p0001

noncomputable def g_tcnc1c
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_cnc (syn_c1c))) (syn_cnc (syn_cpw1 (syn_c1c)))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_tcnc (syn_c1c) p0000
  exact p0001

noncomputable def g_tc11
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (M).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (N).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq M (syn_cnc (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq N (syn_cnc (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_N, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, fresh_x_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, fresh_y_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elncs x M dv_cache_0001
  have p0001 :=
    @g_elncs y N dv_cache_0002
  have p0002 :=
    @g_anbi12i (.classMem M (syn_cncs)) (syn_wex x (.classEq M (syn_cnc (.cv x)))) (.classMem N (syn_cncs)) (syn_wex y (.classEq N (syn_cnc (.cv y)))) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))) x y dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wa (syn_wex x (.classEq M (syn_cnc (.cv x)))) (syn_wex y (.classEq N (syn_cnc (.cv y))))) (syn_wex x (syn_wex y (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))))) p0002 p0003
  have p0005 :=
    @g_vex x
  have p0006 :=
    @g_tcnc (.cv x) p0005
  have p0007 :=
    @g_vex y
  have p0008 :=
    @g_tcnc (.cv y) p0007
  have p0009 :=
    @g_eqeq12i (syn_ctc (syn_cnc (.cv x))) (syn_cnc (syn_cpw1 (.cv x))) (syn_ctc (syn_cnc (.cv y))) (syn_cnc (syn_cpw1 (.cv y))) p0006 p0008
  have p0010 :=
    @g_enpw1 (.cv x) (.cv y)
  have p0011 :=
    @g_eqnc (.cv x) (.cv y) p0005
  have p0012 :=
    @g_pw1ex (.cv x) p0005
  have p0013 :=
    @g_eqnc (syn_cpw1 (.cv x)) (syn_cpw1 (.cv y)) p0012
  have p0014 :=
    @g_n_3bitr4ri (syn_wbr (.cv x) (syn_cen) (.cv y)) (syn_wbr (syn_cpw1 (.cv x)) (syn_cen) (syn_cpw1 (.cv y))) (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y))) (.classEq (syn_cnc (syn_cpw1 (.cv x))) (syn_cnc (syn_cpw1 (.cv y)))) p0010 p0011 p0013
  have p0015 :=
    @g_bitri (.classEq (syn_ctc (syn_cnc (.cv x))) (syn_ctc (syn_cnc (.cv y)))) (.classEq (syn_cnc (syn_cpw1 (.cv x))) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y))) p0009 p0014
  have p0016 :=
    @g_tceq M (syn_cnc (.cv x))
  have p0017 :=
    @g_tceq N (syn_cnc (.cv y))
  have p0018 :=
    @g_eqeqan12d (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))) (syn_ctc M) (syn_ctc (syn_cnc (.cv x))) (syn_ctc N) (syn_ctc (syn_cnc (.cv y))) p0016 p0017
  have p0019 :=
    @g_eqeq12 M (syn_cnc (.cv x)) N (syn_cnc (.cv y))
  have p0020 :=
    @g_bibi12d (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))) (.classEq (syn_ctc M) (syn_ctc N)) (.classEq (syn_ctc (syn_cnc (.cv x))) (syn_ctc (syn_cnc (.cv y)))) (.classEq M N) (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y))) p0018 p0019
  have p0021 :=
    @g_mpbiri (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))) (syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N)) (syn_wb (.classEq (syn_ctc (syn_cnc (.cv x))) (syn_ctc (syn_cnc (.cv y)))) (.classEq (syn_cnc (.cv x)) (syn_cnc (.cv y)))) p0015 p0020
  have p0022 :=
    @g_exlimivv (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))) (syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N)) x y dv_cache_0005 dv_cache_0006 p0021
  have p0023 :=
    @g_sylbi (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wex x (syn_wex y (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))))) (syn_wb (.classEq (syn_ctc M) (syn_ctc N)) (.classEq M N)) p0004 p0022
  exact p0023

#print axioms g_tc11

end NFChoice.DirectNominalPrf.WPPReplay
