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
import NominalWPPReplayChunk017Compact001Part019

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

noncomputable def g_hncodecutinputdecode
    (x : Var) (u : Var) (A : Class) (p : Var) (dv_A_p : p ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_p_u : p ≠ u) (dv_p_x : p ≠ x) (dv_u_x : u ≠ x) :
    Nominal.NPrf (.imp (.classMem (.cv p) (syn_chncodecutinputs A)) (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({p} : Finset Var)
  let y : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let v : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_p : y ≠ p := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_ne_u : q ≠ u := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_q : u ≠ q :=
    Ne.symm fresh_q_ne_u
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_p : v ≠ p := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_v : p ≠ v :=
    Ne.symm fresh_v_ne_p
  have fresh_y_ne_q : y ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_y_ne_v : y ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_v_ne_y : v ≠ y :=
    Ne.symm fresh_y_ne_v
  have fresh_q_ne_v : q ≠ v := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_v_ne_q : v ≠ q :=
    Ne.symm fresh_q_ne_v
  have dv_cache_0001 : y ∉ ((Class.cv p)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_clnpwquoinputfn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : v ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((Wff.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_p_u), fresh_u_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : v ∉ ((Wff.imp (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)) (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_q, fresh_v_ne_y, fresh_v_ne_p, fresh_v_not_A, fresh_v_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((Wff.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_y, fresh_q_not_A, fresh_q_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_p, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : p ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show p ≠ x from (by exact dv_p_x))
  have dv_cache_0017 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show u ≠ x from (by exact dv_u_x))
  have p0000 :=
    (by simpa [syn_chncodecutinputs] using (Nominal.classEqRefl (syn_chncodecutinputs A)))
  have p0001 :=
    @g_eleq2i (syn_chncodecutinputs A) (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) (.cv p) p0000
  have p0002 :=
    @g_biimpi (.classMem (.cv p) (syn_chncodecutinputs A)) (.classMem (.cv p) (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))) p0001
  have p0003 :=
    @g_eluni y (.cv p) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))) dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_sylib (.classMem (.cv p) (syn_chncodecutinputs A)) (.classMem (.cv p) (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))) (syn_wex y (syn_wa (.classMem (.cv p) (.cv y)) (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))) p0002 p0003
  have p0005 :=
    @g_simpl (.classMem (.cv p) (.cv y)) (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))
  have p0006 :=
    @g_simpr (.classMem (.cv p) (.cv y)) (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))
  have p0007 :=
    @g_lnpwquoinputfnfn
  have p0008 :=
    @g_fnfun (syn_cvv) (syn_clnpwquoinputfn)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_fvelima q (.cv y) (syn_cpw1 (syn_chwcn A)) (syn_clnpwquoinputfn) dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0011 :=
    @g_mpan (syn_wfun (syn_clnpwquoinputfn)) (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) p0009 p0010
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv p) (.cv y)) (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))) (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) p0006 p0011
  have p0013 :=
    @g_elpw1 v (.cv q) (syn_chwcn A) dv_cache_0006 dv_cache_0007
  have p0014 :=
    @g_simpl (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))
  have p0015 :=
    @g_n_3simpa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
  have p0016 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
  have p0017 :=
    @g_syl (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))) (.classMem (.cv v) (syn_chwcn A)) p0015 p0016
  have p0018 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv v) (syn_chwcn A)) p0014 p0017
  have p0019 :=
    @g_simpr (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))
  have p0020 :=
    @g_simpl (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))
  have p0021 :=
    @g_n_3simpc (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
  have p0022 :=
    @g_simpr (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
  have p0023 :=
    @g_syl (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (syn_wa (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)) p0021 p0022
  have p0024 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)) p0020 p0023
  have p0025 :=
    @g_eqcomd (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y) p0024
  have p0026 :=
    @g_simpl (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))
  have p0027 :=
    @g_n_3simpa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
  have p0028 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
  have p0029 :=
    @g_syl (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))) (.classEq (.cv q) (syn_csn (.cv v))) p0027 p0028
  have p0030 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classEq (.cv q) (syn_csn (.cv v))) p0026 p0029
  have p0031 :=
    @g_id (.classEq (.cv q) (syn_csn (.cv v)))
  have p0032 :=
    @g_fveq2d (.classEq (.cv q) (syn_csn (.cv v))) (.cv q) (syn_csn (.cv v)) (syn_clnpwquoinputfn) p0031
  have p0033 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (syn_cfv (syn_clnpwquoinputfn) (syn_csn (.cv v)))) p0030 p0032
  have p0034 :=
    @g_simpl (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))
  have p0035 :=
    @g_n_3simpa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
  have p0036 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
  have p0037 :=
    @g_syl (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))) (.classMem (.cv v) (syn_chwcn A)) p0035 p0036
  have p0038 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv v) (syn_chwcn A)) p0034 p0037
  have p0039 :=
    @g_lnpwquoinputfnvalhwcn v A dv_cache_0008
  have p0040 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cfv (syn_clnpwquoinputfn) (syn_csn (.cv v))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0038 p0039
  have p0041 :=
    @g_eqtrd (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (syn_cfv (syn_clnpwquoinputfn) (syn_csn (.cv v))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0033 p0040
  have p0042 :=
    @g_eqtrd (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (.cv y) (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0025 p0041
  have p0043 :=
    @g_eleqtrd (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (.cv p) (.cv y) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0019 p0042
  have p0044 :=
    @g_jca (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0018 p0043
  have p0045 :=
    @g_id (.classEq (.cv u) (.cv v))
  have p0046 :=
    @g_sneqd (.classEq (.cv u) (.cv v)) (.cv u) (.cv v) p0045
  have p0047 :=
    @g_id (.classEq (.cv u) (.cv v))
  have p0048 :=
    @g_fveq2d (.classEq (.cv u) (.cv v)) (.cv u) (.cv v) (syn_c2nd) p0047
  have p0049 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
  have p0050 :=
    @g_syl (.classEq (.cv u) (.cv v)) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0048 p0049
  have p0051 :=
    @g_xpeq12d (.classEq (.cv u) (.cv v)) (syn_csn (.cv u)) (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) p0046 p0050
  have p0052 :=
    @g_eleq2d (.classEq (.cv u) (.cv v)) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.cv p) p0051
  have p0053 :=
    @g_rspcev (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) u (.cv v) (syn_chwcn A) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0052
  have p0054 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) p0044 p0053
  have p0055 :=
    @g_ex (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) p0054
  have p0056 :=
    @g_n_3exp (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)) (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) p0055
  have p0057 :=
    @g_rexlimiv (.classEq (.cv q) (syn_csn (.cv v))) (.imp (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)) (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))) v (syn_chwcn A) dv_cache_0012 p0056
  have p0058 :=
    @g_sylbi (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_wrex v (syn_chwcn A) (.classEq (.cv q) (syn_csn (.cv v)))) (.imp (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)) (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))) p0013 p0057
  have p0059 :=
    @g_rexlimiv (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)) (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) q (syn_cpw1 (syn_chwcn A)) dv_cache_0013 p0058
  have p0060 :=
    @g_syl (syn_wa (.classMem (.cv p) (.cv y)) (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))) (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) p0012 p0059
  have p0061 :=
    @g_mpd (syn_wa (.classMem (.cv p) (.cv y)) (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))) (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) p0005 p0060
  have p0062 :=
    @g_exlimiv (syn_wa (.classMem (.cv p) (.cv y)) (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) y dv_cache_0014 p0061
  have p0063 :=
    @g_syl (.classMem (.cv p) (syn_chncodecutinputs A)) (syn_wex y (syn_wa (.classMem (.cv p) (.cv y)) (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) p0004 p0062
  have p0064 :=
    @g_hncodeinputproductdecode x u (syn_cfv (syn_c2nd) (.cv u)) p dv_cache_0015 dv_cache_0016 dv_cache_0017
  have p0065 :=
    @g_reximi (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) u (syn_chwcn A) p0064
  have p0066 :=
    @g_syl (.classMem (.cv p) (syn_chncodecutinputs A)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))) p0063 p0065
  exact p0066

noncomputable def g_hncodecutpairfnvalhwcn
    (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_chncodecutpairfn) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_hwcnpair u A
  have p0001 :=
    @g_opeq1d (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv x)) p0000
  have p0002 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn A)) (syn_cop (.cv u) (syn_csn (.cv x))) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv x))) (syn_chncodecutpairfn) p0001
  have p0003 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0004 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0005 :=
    @g_hncodecutpairfnval x (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) p0003 p0004
  have p0006 :=
    @g_a1i (.classEq (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) p0005
  have p0007 :=
    @g_hwcnpair u A
  have p0008 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0007
  have p0009 :=
    @g_opeq2d (.classMem (.cv u) (syn_chwcn A)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (.cv u) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) p0008
  have p0010 :=
    @g_n_3eqtrd (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_chncodecutpairfn) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u)) p0002 p0006 p0009
  exact p0010

#print axioms g_hncodecutpairfnvalhwcn

end NFChoice.DirectNominalPrf.WPPReplay
