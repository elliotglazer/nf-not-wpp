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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk009StructuralPart034


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

noncomputable def g_nndisjeq
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let q : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let b : Var := freshVar proofSupport 5
  let x : Var := freshVar proofSupport 6
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (h))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_n_ne_p : n ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_n : p ≠ n :=
    Ne.symm fresh_n_ne_p
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_n_ne_q : n ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_q_ne_n : q ≠ n :=
    Ne.symm fresh_n_ne_q
  have fresh_n_ne_a : n ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_n : a ≠ n :=
    Ne.symm fresh_n_ne_a
  have fresh_n_ne_b : n ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_b_ne_n : b ≠ n :=
    Ne.symm fresh_n_ne_b
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have fresh_p_ne_m : p ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_p : m ≠ p :=
    Ne.symm fresh_p_ne_m
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have fresh_p_ne_a : p ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_p : a ≠ p :=
    Ne.symm fresh_p_ne_a
  have fresh_p_ne_b : p ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_b_ne_p : b ≠ p :=
    Ne.symm fresh_p_ne_b
  have fresh_p_ne_x : p ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_m_ne_q : m ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_q_ne_m : q ≠ m :=
    Ne.symm fresh_m_ne_q
  have fresh_m_ne_a : m ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_m : a ≠ m :=
    Ne.symm fresh_m_ne_a
  have fresh_m_ne_b : m ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_b_ne_m : b ≠ m :=
    Ne.symm fresh_m_ne_b
  have fresh_m_ne_x : m ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_x_ne_m : x ≠ m :=
    Ne.symm fresh_m_ne_x
  have fresh_q_ne_a : q ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_q : a ≠ q :=
    Ne.symm fresh_q_ne_a
  have fresh_q_ne_b : q ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_b_ne_q : b ≠ q :=
    Ne.symm fresh_q_ne_b
  have fresh_q_ne_x : q ≠ x := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have p0000 :=
    @g_vex p
  have p0001 :=
    @g_elcompl (.cv p) (syn_cimak (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc)) p0000
  have p0002 :=
    @g_elimak n (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc) (.cv p) (by exact (show n ∉ ((syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show n ∉ ((syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show n ∉ (((syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) ∪ (((syn_cidk)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show n ∉ ((syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show n ∉ (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show n ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show n ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show n ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show n ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))) (show n ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show n ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show n ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))) (show n ∉ ((syn_cidk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) (by exact (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ p from (by exact fresh_n_ne_p))))))) p0000
  have p0003 :=
    @g_opkex (.cv n) (.cv p)
  have p0004 :=
    @g_elcompl (syn_copk (.cv n) (.cv p)) (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)) p0003
  have p0005 :=
    @g_elun (syn_copk (.cv n) (.cv p)) (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)
  have p0006 :=
    @g_vex n
  have p0007 :=
    @g_ndisjrelk (.cv n) (.cv p) p0006 p0000
  have p0008 :=
    @g_notbii (.classMem (syn_copk (.cv n) (.cv p)) (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wne (syn_cin (.cv n) (.cv p)) (syn_c0)) p0007
  have p0009 :=
    @g_elcompl (syn_copk (.cv n) (.cv p)) (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0010 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cin (.cv n) (.cv p)) (syn_c0))))
  have p0011 :=
    @g_con2bii (syn_wne (syn_cin (.cv n) (.cv p)) (syn_c0)) (.classEq (syn_cin (.cv n) (.cv p)) (syn_c0)) p0010
  have p0012 :=
    @g_n_3bitr4i (.neg (.classMem (syn_copk (.cv n) (.cv p)) (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.neg (syn_wne (syn_cin (.cv n) (.cv p)) (syn_c0))) (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq (syn_cin (.cv n) (.cv p)) (syn_c0)) p0008 p0009 p0011
  have p0013 :=
    @g_opkelidkg (.cv n) (.cv p) (syn_cvv) (syn_cvv)
  have p0014_e02_recanon : Nominal.NPrf (.imp (syn_wa (.classMem (.cv n) (syn_cvv)) (.classMem (.cv p) (syn_cvv))) (syn_wb (.classMem (syn_copk (.cv n) (.cv p)) (syn_cidk)) (.objEq n p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cvv syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cidk syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0013
  have p0014 :=
    @g_mp2an (.classMem (.cv n) (syn_cvv)) (.classMem (.cv p) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv n) (.cv p)) (syn_cidk)) (.objEq n p)) p0006 p0000 p0014_e02_recanon
  have p0015 :=
    @g_orbi12i (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq (syn_cin (.cv n) (.cv p)) (syn_c0)) (.classMem (syn_copk (.cv n) (.cv p)) (syn_cidk)) (.objEq n p) p0012 p0014
  have p0016 :=
    @g_incom (.cv n) (.cv p)
  have p0017 :=
    @g_eqeq1i (syn_cin (.cv n) (.cv p)) (syn_cin (.cv p) (.cv n)) (syn_c0) p0016
  have p0018 :=
    @g_eqcom (.cv n) (.cv p)
  have p0019_e01_recanon : Nominal.NPrf (syn_wb (.objEq n p) (.objEq p n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0018
  have p0019 :=
    @g_orbi12i (.classEq (syn_cin (.cv n) (.cv p)) (syn_c0)) (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq n p) (.objEq p n) p0017 p0019_e01_recanon
  have p0020 :=
    @g_n_3bitri (.classMem (syn_copk (.cv n) (.cv p)) (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_wo (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classMem (syn_copk (.cv n) (.cv p)) (syn_cidk))) (syn_wo (.classEq (syn_cin (.cv n) (.cv p)) (syn_c0)) (.objEq n p)) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)) p0005 p0015 p0019
  have p0021 :=
    @g_xchbinx (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))) (.classMem (syn_copk (.cv n) (.cv p)) (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)) p0004 p0020
  have p0022 :=
    @g_rexbii (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))) (.neg (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))) n (syn_cnnc) p0021
  have p0023 :=
    @g_rexnal (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)) n (syn_cnnc)
  have p0024 :=
    @g_n_3bitri (.classMem (.cv p) (syn_cimak (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc))) (syn_wrex n (syn_cnnc) (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))))) (syn_wrex n (syn_cnnc) (.neg (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)))) (.neg (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)))) p0002 p0022 p0023
  have p0025 :=
    @g_con2bii (.classMem (.cv p) (syn_cimak (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc))) (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))) p0024
  have p0026 :=
    @g_bitr4i (.classMem (.cv p) (syn_ccompl (syn_cimak (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc)))) (.neg (.classMem (.cv p) (syn_cimak (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc)))) (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))) p0001 p0025
  have p0027 :=
    @g_eqabi (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))) p (syn_ccompl (syn_cimak (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc))) (by exact (show p ∉ ((syn_ccompl (syn_cimak (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show p ∉ ((syn_cimak (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show p ∉ (((syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show p ∉ ((syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show p ∉ (((syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) ∪ (((syn_cidk)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show p ∉ ((syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show p ∉ (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show p ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show p ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show p ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show p ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))) (show p ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show p ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show p ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))) (show p ∉ ((syn_cidk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))) (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) p0026
  have p0028 :=
    @g_ssetkex
  have p0029 :=
    @g_ins3kex (syn_cssetk) p0028
  have p0030 :=
    @g_ssetkex
  have p0031 :=
    @g_ins2kex (syn_cssetk) p0030
  have p0032 :=
    @g_inex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)) p0029 p0031
  have p0033 :=
    @g_n_1cex
  have p0034 :=
    @g_pw1ex (syn_c1c) p0033
  have p0035 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0034
  have p0036 :=
    @g_imakex (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))) p0032 p0035
  have p0037 :=
    @g_complex (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0036
  have p0038 :=
    @g_idkex
  have p0039 :=
    @g_unex (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk) p0037 p0038
  have p0040 :=
    @g_complex (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)) p0039
  have p0041 :=
    @g_nncex
  have p0042 :=
    @g_imakex (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc) p0040 p0041
  have p0043 :=
    @g_complex (syn_cimak (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc)) p0042
  have p0044 :=
    @g_eqeltrri (syn_ccompl (syn_cimak (syn_ccompl (syn_cun (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc))) (.cab p (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)))) (syn_cvv) p0027 p0043
  have p0045 :=
    (by simpa [syn_c0c] using (Nominal.classEqRefl (syn_c0c)))
  have p0046 :=
    @g_eqeq2i (syn_c0c) (syn_csn (syn_c0)) (.cv p) p0045
  have p0047 :=
    @g_biimpi (.classEq (.cv p) (syn_c0c)) (.classEq (.cv p) (syn_csn (syn_c0))) p0046
  have p0048 :=
    @g_ineq1d (.classEq (.cv p) (syn_c0c)) (.cv p) (syn_csn (syn_c0)) (.cv n) p0047
  have p0049 :=
    @g_eqeq1d (.classEq (.cv p) (syn_c0c)) (syn_cin (.cv p) (.cv n)) (syn_cin (syn_csn (syn_c0)) (.cv n)) (syn_c0) p0048
  have p0050 :=
    @g_incom (syn_csn (syn_c0)) (.cv n)
  have p0051 :=
    @g_eqeq1i (syn_cin (syn_csn (syn_c0)) (.cv n)) (syn_cin (.cv n) (syn_csn (syn_c0))) (syn_c0) p0050
  have p0052 :=
    @g_disjsn (.cv n) (syn_c0)
  have p0053 :=
    @g_bitri (.classEq (syn_cin (syn_csn (syn_c0)) (.cv n)) (syn_c0)) (.classEq (syn_cin (.cv n) (syn_csn (syn_c0))) (syn_c0)) (.neg (.classMem (syn_c0) (.cv n))) p0051 p0052
  have p0054 :=
    @g_syl6bb (.classEq (.cv p) (syn_c0c)) (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.classEq (syn_cin (syn_csn (syn_c0)) (.cv n)) (syn_c0)) (.neg (.classMem (syn_c0) (.cv n))) p0049 p0053
  have p0055 :=
    @g_eqeq1 (.cv p) (syn_c0c) (.cv n)
  have p0056 :=
    @g_eqcom (syn_c0c) (.cv n)
  have p0057_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv p) (syn_c0c)) (syn_wb (.objEq p n) (.classEq (syn_c0c) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0055
  have p0057 :=
    @g_syl6bb (.classEq (.cv p) (syn_c0c)) (.objEq p n) (.classEq (syn_c0c) (.cv n)) (.classEq (.cv n) (syn_c0c)) p0057_e00_recanon p0056
  have p0058 :=
    @g_orbi12d (.classEq (.cv p) (syn_c0c)) (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.neg (.classMem (syn_c0) (.cv n))) (.objEq p n) (.classEq (.cv n) (syn_c0c)) p0054 p0057
  have p0059 :=
    @g_ralbidv (.classEq (.cv p) (syn_c0c)) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)) (syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c))) n (syn_cnnc) (by exact (show n ∉ ((Wff.classEq (.cv p) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((Class.cv p)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ p from (by exact fresh_n_ne_p)))))) (show n ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0058
  have p0060 :=
    @g_ineq1 (.cv p) (.cv m) (.cv n)
  have p0061_e00_recanon : Nominal.NPrf (.imp (.objEq p m) (.classEq (syn_cin (.cv p) (.cv n)) (syn_cin (.cv m) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0060
  have p0061 :=
    @g_eqeq1d (.objEq p m) (syn_cin (.cv p) (.cv n)) (syn_cin (.cv m) (.cv n)) (syn_c0) p0061_e00_recanon
  have p0062 :=
    @g_eqeq1 (.cv p) (.cv m) (.cv n)
  have p0063_e01_recanon : Nominal.NPrf (.imp (.objEq p m) (syn_wb (.objEq p n) (.objEq m n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0062
  have p0063 :=
    @g_orbi12d (.objEq p m) (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.objEq p n) (.objEq m n) p0061 p0063_e01_recanon
  have p0064 :=
    @g_ralbidv (.objEq p m) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)) (syn_wo (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.objEq m n)) n (syn_cnnc) (by exact (show n ∉ ((Wff.objEq p m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show n ∉ ({p, m} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show n ≠ p from (by exact fresh_n_ne_p)), (show n ≠ m from (by exact fresh_n_ne_m))⟩))))) p0063
  have p0065 :=
    @g_ineq2 (.cv n) (.cv q) (.cv m)
  have p0066_e00_recanon : Nominal.NPrf (.imp (.objEq n q) (.classEq (syn_cin (.cv m) (.cv n)) (syn_cin (.cv m) (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0065
  have p0066 :=
    @g_eqeq1d (.objEq n q) (syn_cin (.cv m) (.cv n)) (syn_cin (.cv m) (.cv q)) (syn_c0) p0066_e00_recanon
  have p0067 :=
    @g_equequ2 n q m
  have p0068 :=
    @g_orbi12d (.objEq n q) (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m n) (.objEq m q) p0066 p0067
  have p0069 :=
    @g_cbvralv (syn_wo (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.objEq m n)) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)) n q (syn_cnnc) (by exact (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show q ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show q ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.objEq m n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show q ∉ (((Wff.classEq (syn_cin (.cv m) (.cv n)) (syn_c0))).fv) ∪ (((Wff.objEq m n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Wff.classEq (syn_cin (.cv m) (.cv n)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show q ∉ (((syn_cin (.cv m) (.cv n))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((syn_cin (.cv m) (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show q ∉ (((Class.cv m)).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ m from (by exact fresh_q_ne_m)))))) (show q ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ n from (by exact fresh_q_ne_n)))))))))) (show q ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show q ∉ ((Wff.objEq m n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show q ∉ ({m, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show q ≠ m from (by exact fresh_q_ne_m)), (show q ≠ n from (by exact fresh_q_ne_n))⟩))))))))) (by exact (show n ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show n ∉ (((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv) ∪ (((Wff.objEq m q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((syn_cin (.cv m) (.cv q))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cin (.cv m) (.cv q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show n ∉ (((Class.cv m)).fv) ∪ (((Class.cv q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ m from (by exact fresh_n_ne_m)))))) (show n ∉ ((Class.cv q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({q} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ q from (by exact fresh_n_ne_q)))))))))) (show n ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show n ∉ ((Wff.objEq m q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show n ∉ ({m, q} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show n ≠ m from (by exact fresh_n_ne_m)), (show n ≠ q from (by exact fresh_n_ne_q))⟩))))))))) p0068
  have p0070 :=
    @g_syl6bb (.objEq p m) (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))) (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.objEq m n))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) p0064 p0069
  have p0071 :=
    @g_ineq1 (.cv p) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0072 :=
    @g_eqeq1d (.classEq (.cv p) (syn_cplc (.cv m) (syn_c1c))) (syn_cin (.cv p) (.cv n)) (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0) p0071
  have p0073 :=
    @g_eqeq1 (.cv p) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0074_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv p) (syn_cplc (.cv m) (syn_c1c))) (syn_wb (.objEq p n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0073
  have p0074 :=
    @g_orbi12d (.classEq (.cv p) (syn_cplc (.cv m) (syn_c1c))) (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.objEq p n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0072 p0074_e01_recanon
  have p0075 :=
    @g_ralbidv (.classEq (.cv p) (syn_cplc (.cv m) (syn_c1c))) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)) (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) n (syn_cnnc) (by exact (show n ∉ ((Wff.classEq (.cv p) (syn_cplc (.cv m) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((Class.cv p)).fv) ∪ (((syn_cplc (.cv m) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ p from (by exact fresh_n_ne_p)))))) (show n ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show n ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ m from (by exact fresh_n_ne_m)))))) (show n ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0074
  have p0076 :=
    @g_ineq1 (.cv p) M (.cv n)
  have p0077 :=
    @g_eqeq1d (.classEq (.cv p) M) (syn_cin (.cv p) (.cv n)) (syn_cin M (.cv n)) (syn_c0) p0076
  have p0078 :=
    @g_eqeq1 (.cv p) M (.cv n)
  have p0079_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv p) M) (syn_wb (.objEq p n) (.classEq M (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0078
  have p0079 :=
    @g_orbi12d (.classEq (.cv p) M) (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.classEq (syn_cin M (.cv n)) (syn_c0)) (.objEq p n) (.classEq M (.cv n)) p0077 p0079_e01_recanon
  have p0080 :=
    @g_ralbidv (.classEq (.cv p) M) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)) (syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n))) n (syn_cnnc) (by exact (show n ∉ ((Wff.classEq (.cv p) M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((Class.cv p)).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ p from (by exact fresh_n_ne_p)))))) (show n ∉ (M).fv from (by exact fresh_n_not_M))))))) p0079
  have p0081 :=
    @g_nnc0suc m (.cv n) (by exact (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact fresh_m_ne_n)))))))
  have p0082 :=
    @g_n_0nelsuc (.cv m)
  have p0083 :=
    @g_eleq2 (.cv n) (syn_cplc (.cv m) (syn_c1c)) (syn_c0)
  have p0084 :=
    @g_biimpcd (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_c0) (.cv n)) (.classMem (syn_c0) (syn_cplc (.cv m) (syn_c1c))) p0083
  have p0085 :=
    @g_mtoi (.classMem (syn_c0) (.cv n)) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_c0) (syn_cplc (.cv m) (syn_c1c))) p0082 p0084
  have p0086 :=
    @g_adantr (.classMem (syn_c0) (.cv n)) (.neg (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))) (.classMem (.cv m) (syn_cnnc)) p0085
  have p0087 :=
    @g_nrexdv (.classMem (syn_c0) (.cv n)) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) m (syn_cnnc) (by exact (show m ∉ ((Wff.classMem (syn_c0) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((syn_c0)).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact fresh_m_ne_n))))))))))) p0086
  have p0088 :=
    @g_orel2 (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))) (.classEq (.cv n) (syn_c0c))
  have p0089 :=
    @g_syl (.classMem (syn_c0) (.cv n)) (.neg (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))))) (.imp (syn_wo (.classEq (.cv n) (syn_c0c)) (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))))) (.classEq (.cv n) (syn_c0c))) p0087 p0088
  have p0090 :=
    @g_com12 (.classMem (syn_c0) (.cv n)) (syn_wo (.classEq (.cv n) (syn_c0c)) (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))))) (.classEq (.cv n) (syn_c0c)) p0089
  have p0091 :=
    @g_sylbi (.classMem (.cv n) (syn_cnnc)) (syn_wo (.classEq (.cv n) (syn_c0c)) (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))))) (.imp (.classMem (syn_c0) (.cv n)) (.classEq (.cv n) (syn_c0c))) p0081 p0090
  have p0092 :=
    @g_imor (.classMem (syn_c0) (.cv n)) (.classEq (.cv n) (syn_c0c))
  have p0093 :=
    @g_sylib (.classMem (.cv n) (syn_cnnc)) (.imp (.classMem (syn_c0) (.cv n)) (.classEq (.cv n) (syn_c0c))) (syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c))) p0091 p0092
  have p0094 :=
    @g_rgen (syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c))) n (syn_cnnc) p0093
  have p0095 :=
    @g_neq0 a (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (by exact (show a ∉ ((syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show a ∉ (((syn_cplc (.cv m) (syn_c1c))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact fresh_a_ne_m)))))) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ n from (by exact fresh_a_ne_n)))))))))))
  have p0096 :=
    @g_elin (.cv a) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0097 :=
    @g_elsuc x (.cv a) (.cv m) b (by exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a))))))) (by exact (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a))))))) (by exact (show b ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ m from (by exact fresh_b_ne_m))))))) (show b ≠ x from (by exact fresh_b_ne_x))
  have p0098 :=
    @g_vex x
  have p0099 :=
    @g_elcompl (.cv x) (.cv b) p0098
  have p0100_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0099
  have p0100 :=
    @g_anbi2i (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b)) (.objMem b m) p0100_e00_recanon
  have p0101 :=
    @g_simp1r (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))
  have p0102 :=
    @g_nnc0suc p (.cv n) (by exact (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))))
  have p0103 :=
    @g_sylib (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (.cv n) (syn_cnnc)) (syn_wo (.classEq (.cv n) (syn_c0c)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))))) p0101 p0102
  have p0104 :=
    @g_ssun2 (syn_csn (.cv x)) (.cv b)
  have p0105 :=
    @g_snid (.cv x) p0098
  have p0106 :=
    @g_sselii (syn_csn (.cv x)) (syn_cun (.cv b) (syn_csn (.cv x))) (.cv x) p0104 p0105
  have p0107 :=
    @g_n0i (syn_cun (.cv b) (syn_csn (.cv x))) (.cv x)
  have p0108 :=
    Nominal.mp p0106 p0107
  have p0109 :=
    (by simpa [syn_c0c] using (Nominal.classEqRefl (syn_c0c)))
  have p0110 :=
    @g_eleq2i (syn_c0c) (syn_csn (syn_c0)) (syn_cun (.cv b) (syn_csn (.cv x))) p0109
  have p0111 :=
    @g_vex b
  have p0112 :=
    @g_snex (.cv x)
  have p0113 :=
    @g_unex (.cv b) (syn_csn (.cv x)) p0111 p0112
  have p0114 :=
    @g_elsnc (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0) p0113
  have p0115 :=
    @g_bitri (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0c)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_csn (syn_c0))) (.classEq (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0)) p0110 p0114
  have p0116 :=
    @g_mtbir (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0c)) (.classEq (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0)) p0108 p0115
  have p0117 :=
    @g_eleq2 (.cv n) (syn_c0c) (syn_cun (.cv b) (syn_csn (.cv x)))
  have p0118 :=
    @g_biimpcd (.classEq (.cv n) (syn_c0c)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0c)) p0117
  have p0119 :=
    @g_mtoi (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)) (.classEq (.cv n) (syn_c0c)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0c)) p0116 p0118
  have p0120 :=
    @g_adantl (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)) (.neg (.classEq (.cv n) (syn_c0c))) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) p0119
  have p0121 :=
    @g_orel1 (.classEq (.cv n) (syn_c0c)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))))
  have p0122 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))) (.neg (.classEq (.cv n) (syn_c0c))) (.imp (syn_wo (.classEq (.cv n) (syn_c0c)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))))) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))))) p0120 p0121
  have p0123 :=
    @g_simpll (.classMem (.cv p) (syn_cnnc)) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
  have p0124 :=
    @g_simpr3r (.objMem b m) (.neg (.objMem x b)) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (.classMem (.cv p) (syn_cnnc))
  have p0125 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b))))) (.neg (.objMem x b)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))) p0124
  have p0126 :=
    @g_simpr (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b))))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
  have p0127 :=
    @g_nnsucelr (.cv b) (.cv p) (.cv x) p0111 p0098
  have p0128_e03_recanon : Nominal.NPrf (.imp (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.neg (.objMem x b)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))))) (.objMem b p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0127
  have p0128 :=
    @g_syl12anc (syn_wa (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b))))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))) (.classMem (.cv p) (syn_cnnc)) (.neg (.objMem x b)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))) (.objMem b p) p0123 p0125 p0126 p0128_e03_recanon
  have p0129 :=
    @g_ex (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b))))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))) (.objMem b p) p0128
  have p0130 :=
    @g_ineq2 (.cv q) (.cv p) (.cv m)
  have p0131_e00_recanon : Nominal.NPrf (.imp (.objEq q p) (.classEq (syn_cin (.cv m) (.cv q)) (syn_cin (.cv m) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0130
  have p0131 :=
    @g_eqeq1d (.objEq q p) (syn_cin (.cv m) (.cv q)) (syn_cin (.cv m) (.cv p)) (syn_c0) p0131_e00_recanon
  have p0132 :=
    @g_equequ2 q p m
  have p0133 :=
    @g_orbi12d (.objEq q p) (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m q) (.objEq m p) p0131 p0132
  have p0134_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv q) (.cv p)) (syn_wb (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)) (syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wo syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_c0 syn_cdif syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0133
  have p0134 :=
    @g_rspccv (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)) (syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p)) q (.cv p) (syn_cnnc) (by exact (show q ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ p from (by exact fresh_q_ne_p))))))) (by exact (show q ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show q ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show q ∉ (((Wff.classEq (syn_cin (.cv m) (.cv p)) (syn_c0))).fv) ∪ (((Wff.objEq m p)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Wff.classEq (syn_cin (.cv m) (.cv p)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show q ∉ (((syn_cin (.cv m) (.cv p))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((syn_cin (.cv m) (.cv p))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show q ∉ (((Class.cv m)).fv) ∪ (((Class.cv p)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ m from (by exact fresh_q_ne_m)))))) (show q ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ p from (by exact fresh_q_ne_p)))))))))) (show q ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show q ∉ ((Wff.objEq m p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show q ∉ ({m, p} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show q ≠ m from (by exact fresh_q_ne_m)), (show q ≠ p from (by exact fresh_q_ne_p))⟩))))))))) p0134_e00_recanon
  have p0135 :=
    @g_elin (.cv b) (.cv m) (.cv p)
  have p0136 :=
    @g_n0i (syn_cin (.cv m) (.cv p)) (.cv b)
  have p0137_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv b) (syn_cin (.cv m) (.cv p))) (syn_wa (.objMem b m) (.objMem b p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0135
  have p0137 :=
    @g_sylbir (syn_wa (.objMem b m) (.objMem b p)) (.classMem (.cv b) (syn_cin (.cv m) (.cv p))) (.neg (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0))) p0137_e00_recanon p0136
  have p0138 :=
    @g_pm2_53 (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p)
  have p0139 :=
    @g_syl5 (syn_wa (.objMem b m) (.objMem b p)) (.neg (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0))) (syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p)) (.objEq m p) p0137 p0138
  have p0140 :=
    @g_exp3a (syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p)) (.objMem b m) (.objMem b p) (.objEq m p) p0139
  have p0141 :=
    @g_syl6 (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (.classMem (.cv p) (syn_cnnc)) (syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p)) (.imp (.objMem b m) (.imp (.objMem b p) (.objEq m p))) p0134 p0140
  have p0142 :=
    @g_com23 (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (.classMem (.cv p) (syn_cnnc)) (.objMem b m) (.imp (.objMem b p) (.objEq m p)) p0141
  have p0143 :=
    @g_imp (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (.objMem b m) (.imp (.classMem (.cv p) (syn_cnnc)) (.imp (.objMem b p) (.objEq m p))) p0142
  have p0144 :=
    @g_adantrr (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (.objMem b m) (.imp (.classMem (.cv p) (syn_cnnc)) (.imp (.objMem b p) (.objEq m p))) (.neg (.objMem x b)) p0143
  have p0145 :=
    @g_n_3adant1 (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b))) (.imp (.classMem (.cv p) (syn_cnnc)) (.imp (.objMem b p) (.objEq m p))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) p0144
  have p0146 :=
    @g_impcom (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (.cv p) (syn_cnnc)) (.imp (.objMem b p) (.objEq m p)) p0145
  have p0147 :=
    @g_syld (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b))))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))) (.objMem b p) (.objEq m p) p0129 p0146
  have p0148 :=
    @g_ex (.classMem (.cv p) (syn_cnnc)) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.imp (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))) (.objEq m p)) p0147
  have p0149 :=
    @g_com3l (.classMem (.cv p) (syn_cnnc)) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))) (.objEq m p) p0148
  have p0150 :=
    @g_imp (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))) (.imp (.classMem (.cv p) (syn_cnnc)) (.objEq m p)) p0149
  have p0151 :=
    @g_addceq1 (.cv m) (.cv p) (syn_c1c)
  have p0152_e01_recanon : Nominal.NPrf (.imp (.objEq m p) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv p) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0151
  have p0152 :=
    @g_syl6 (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))) (.classMem (.cv p) (syn_cnnc)) (.objEq m p) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv p) (syn_c1c))) p0150 p0152_e01_recanon
  have p0153 :=
    @g_eleq2 (.cv n) (syn_cplc (.cv p) (syn_c1c)) (syn_cun (.cv b) (syn_csn (.cv x)))
  have p0154 :=
    @g_anbi2d (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) p0153
  have p0155 :=
    @g_eqeq2 (.cv n) (syn_cplc (.cv p) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))
  have p0156 :=
    @g_imbi2d (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv p) (syn_c1c))) (.classMem (.cv p) (syn_cnnc)) p0155
  have p0157 :=
    @g_imbi12d (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))) (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))) (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))) (.imp (.classMem (.cv p) (syn_cnnc)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (.imp (.classMem (.cv p) (syn_cnnc)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv p) (syn_c1c)))) p0154 p0156
  have p0158 :=
    @g_mpbiri (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))) (.imp (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))) (.imp (.classMem (.cv p) (syn_cnnc)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))) (.imp (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))) (.imp (.classMem (.cv p) (syn_cnnc)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv p) (syn_c1c))))) p0152 p0157
  have p0159 :=
    @g_com3l (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))) (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))) (.classMem (.cv p) (syn_cnnc)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0158
  have p0160 :=
    @g_rexlimdv (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p (syn_cnnc) (by exact (show p ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show p ∉ (((syn_cplc (.cv m) (syn_c1c))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show p ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ m from (by exact fresh_p_ne_m)))))) (show p ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n))))))))))) (by exact (show p ∉ ((syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show p ∉ (((syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b))))).fv) ∪ (((Wff.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show p ∉ (((syn_wa (.objMem b m) (.neg (.objMem x b)))).fv) ∪ (((syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))).fv) ∪ (((syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_wa (.objMem b m) (.neg (.objMem x b)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show p ∉ (((Wff.objMem b m)).fv) ∪ (((Wff.neg (.objMem x b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.objMem b m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show p ∉ ({b, m} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show p ≠ b from (by exact fresh_p_ne_b)), (show p ≠ m from (by exact fresh_p_ne_m))⟩)))) (show p ∉ ((Wff.neg (.objMem x b))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show p ∉ ((Wff.objMem x b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show p ∉ ({x, b} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show p ≠ x from (by exact fresh_p_ne_x)), (show p ≠ b from (by exact fresh_p_ne_b))⟩)))))))))) (show p ∉ ((syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show p ∉ (((Wff.classMem (.cv m) (syn_cnnc))).fv) ∪ (((Wff.classMem (.cv n) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.classMem (.cv m) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ (((Class.cv m)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ m from (by exact fresh_p_ne_m)))))) (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show p ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))) (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (show p ∉ ((syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show p ∉ ((((syn_cnnc)).fv).erase q) ∪ ((((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (((syn_cnnc)).fv).erase q from (fun hmem => (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show p ∉ (((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q from (fun hmem => (show p ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show p ∉ (((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv) ∪ (((Wff.objEq m q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show p ∉ (((syn_cin (.cv m) (.cv q))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cin (.cv m) (.cv q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show p ∉ (((Class.cv m)).fv) ∪ (((Class.cv q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ m from (by exact fresh_p_ne_m)))))) (show p ∉ ((Class.cv q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({q} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ q from (by exact fresh_p_ne_q)))))))))) (show p ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show p ∉ ((Wff.objEq m q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show p ∉ ({m, q} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show p ≠ m from (by exact fresh_p_ne_m)), (show p ≠ q from (by exact fresh_p_ne_q))⟩)))))))) (Finset.mem_of_mem_erase hmem))))))))))) (show p ∉ ((Wff.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ (((syn_cun (.cv b) (syn_csn (.cv x)))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cun (.cv b) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show p ∉ (((Class.cv b)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ b from (by exact fresh_p_ne_b)))))) (show p ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show p ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ x from (by exact fresh_p_ne_x)))))))))))) (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n))))))))))))))) p0159
  have p0161 :=
    @g_syld (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))) (syn_wo (.classEq (.cv n) (syn_c0c)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))))) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0122 p0160
  have p0162 :=
    @g_ex (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)) (.imp (syn_wo (.classEq (.cv n) (syn_c0c)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) p0161
  have p0163 :=
    @g_mpid (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)) (syn_wo (.classEq (.cv n) (syn_c0c)) (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0103 p0162
  have p0164 :=
    @g_n_3expa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wa (.objMem b m) (.neg (.objMem x b))) (.imp (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) p0163
  have p0165 :=
    @g_eleq1 (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)
  have p0166_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (syn_wb (.objMem a n) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0165
  have p0166 :=
    @g_imbi1d (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (.objMem a n) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0166_e00_recanon
  have p0167 :=
    @g_syl5ibrcom (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))) (syn_wa (.objMem b m) (.neg (.objMem x b)))) (.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (.imp (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) p0164 p0166
  have p0168 :=
    @g_sylan2b (syn_wa (.objMem b m) (.classMem (.cv x) (syn_ccompl (.cv b)))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))) (syn_wa (.objMem b m) (.neg (.objMem x b))) (.imp (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))) p0100 p0167
  have p0169_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))) (syn_wa (.classMem (.cv b) (.cv m)) (.classMem (.cv x) (syn_ccompl (.cv b))))) (.imp (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0168
  have p0169 :=
    @g_rexlimdvva (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) b x (.cv m) (syn_ccompl (.cv b)) (by exact (show x ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ m from (by exact fresh_x_ne_m))))))) (by exact (show b ∉ ((Wff.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.objMem a n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show b ∉ ({a, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ a from (by exact fresh_b_ne_a)), (show b ≠ n from (by exact fresh_b_ne_n))⟩)))) (show b ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((syn_cplc (.cv m) (syn_c1c))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ m from (by exact fresh_b_ne_m)))))) (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ n from (by exact fresh_b_ne_n))))))))))))))) (by exact (show x ∉ ((Wff.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show x ∉ (((Wff.objMem a n)).fv) ∪ (((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.objMem a n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show x ∉ ({a, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show x ≠ a from (by exact fresh_x_ne_a)), (show x ≠ n from (by exact fresh_x_ne_n))⟩)))) (show x ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_cplc (.cv m) (syn_c1c))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ m from (by exact fresh_x_ne_m)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ n from (by exact fresh_x_ne_n))))))))))))))) (by exact (show b ∉ ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))).fv) ∪ (((syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.classMem (.cv m) (syn_cnnc))).fv) ∪ (((Wff.classMem (.cv n) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem (.cv m) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv m)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ m from (by exact fresh_b_ne_m)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ n from (by exact fresh_b_ne_n)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show b ∉ ((syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show b ∉ ((((syn_cnnc)).fv).erase q) ∪ ((((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (((syn_cnnc)).fv).erase q from (fun hmem => (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show b ∉ (((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q from (fun hmem => (show b ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show b ∉ (((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv) ∪ (((Wff.objEq m q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((syn_cin (.cv m) (.cv q))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cin (.cv m) (.cv q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show b ∉ (((Class.cv m)).fv) ∪ (((Class.cv q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ m from (by exact fresh_b_ne_m)))))) (show b ∉ ((Class.cv q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({q} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ q from (by exact fresh_b_ne_q)))))))))) (show b ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.objEq m q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show b ∉ ({m, q} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ m from (by exact fresh_b_ne_m)), (show b ≠ q from (by exact fresh_b_ne_q))⟩)))))))) (Finset.mem_of_mem_erase hmem)))))))))))) (by exact (show x ∉ ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))).fv) ∪ (((syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classMem (.cv m) (syn_cnnc))).fv) ∪ (((Wff.classMem (.cv n) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem (.cv m) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv m)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ m from (by exact fresh_x_ne_m)))))) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ n from (by exact fresh_x_ne_n)))))) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show x ∉ ((syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show x ∉ ((((syn_cnnc)).fv).erase q) ∪ ((((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (((syn_cnnc)).fv).erase q from (fun hmem => (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show x ∉ (((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q from (fun hmem => (show x ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show x ∉ (((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv) ∪ (((Wff.objEq m q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_cin (.cv m) (.cv q))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cin (.cv m) (.cv q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ (((Class.cv m)).fv) ∪ (((Class.cv q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ m from (by exact fresh_x_ne_m)))))) (show x ∉ ((Class.cv q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({q} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ q from (by exact fresh_x_ne_q)))))))))) (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.objEq m q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show x ∉ ({m, q} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show x ≠ m from (by exact fresh_x_ne_m)), (show x ≠ q from (by exact fresh_x_ne_q))⟩)))))))) (Finset.mem_of_mem_erase hmem)))))))))))) (show b ≠ x from (by exact fresh_b_ne_x)) p0169_e00_recanon
  have p0170 :=
    @g_syl5bi (.classMem (.cv a) (syn_cplc (.cv m) (syn_c1c))) (syn_wrex b (.cv m) (syn_wrex x (syn_ccompl (.cv b)) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))) (.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) p0097 p0169
  have p0171 :=
    @g_imp3a (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))) (.classMem (.cv a) (syn_cplc (.cv m) (syn_c1c))) (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0170
  have p0172_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv a) (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (syn_wa (.classMem (.cv a) (syn_cplc (.cv m) (syn_c1c))) (.objMem a n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0096
  have p0172 :=
    @g_syl5bi (.classMem (.cv a) (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (syn_wa (.classMem (.cv a) (syn_cplc (.cv m) (syn_c1c))) (.objMem a n)) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0172_e00_recanon p0171
  have p0173 :=
    @g_exlimdv (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))) (.classMem (.cv a) (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) a (by exact (show a ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_cplc (.cv m) (syn_c1c))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact fresh_a_ne_m)))))) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ n from (by exact fresh_a_ne_n))))))))))) (by exact (show a ∉ ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))).fv) ∪ (((syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.classMem (.cv m) (syn_cnnc))).fv) ∪ (((Wff.classMem (.cv n) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classMem (.cv m) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((Class.cv m)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact fresh_a_ne_m)))))) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ n from (by exact fresh_a_ne_n)))))) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show a ∉ ((syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show a ∉ ((((syn_cnnc)).fv).erase q) ∪ ((((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (((syn_cnnc)).fv).erase q from (fun hmem => (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show a ∉ (((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q from (fun hmem => (show a ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show a ∉ (((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv) ∪ (((Wff.objEq m q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_cin (.cv m) (.cv q))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cin (.cv m) (.cv q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show a ∉ (((Class.cv m)).fv) ∪ (((Class.cv q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact fresh_a_ne_m)))))) (show a ∉ ((Class.cv q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({q} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ q from (by exact fresh_a_ne_q)))))))))) (show a ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.objEq m q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show a ∉ ({m, q} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ m from (by exact fresh_a_ne_m)), (show a ≠ q from (by exact fresh_a_ne_q))⟩)))))))) (Finset.mem_of_mem_erase hmem)))))))))))) p0172
  have p0174 :=
    @g_syl5bi (.neg (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0))) (syn_wex a (.classMem (.cv a) (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0095 p0173
  have p0175 :=
    @g_orrd (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))) (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0174
  have p0176 :=
    @g_exp31 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) p0175
  have p0177 :=
    @g_com23 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) p0176
  have p0178 :=
    @g_ralrimdv (.classMem (.cv m) (syn_cnnc)) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) n (syn_cnnc) (by exact (show n ∉ ((Wff.classMem (.cv m) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((Class.cv m)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ m from (by exact fresh_n_ne_m)))))) (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show n ∉ ((syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show n ∉ ((((syn_cnnc)).fv).erase q) ∪ ((((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (((syn_cnnc)).fv).erase q from (fun hmem => (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show n ∉ (((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q from (fun hmem => (show n ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show n ∉ (((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv) ∪ (((Wff.objEq m q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((syn_cin (.cv m) (.cv q))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cin (.cv m) (.cv q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show n ∉ (((Class.cv m)).fv) ∪ (((Class.cv q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ m from (by exact fresh_n_ne_m)))))) (show n ∉ ((Class.cv q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({q} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ q from (by exact fresh_n_ne_q)))))))))) (show n ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show n ∉ ((Wff.objEq m q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show n ∉ ({m, q} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show n ≠ m from (by exact fresh_n_ne_m)), (show n ≠ q from (by exact fresh_n_ne_q))⟩)))))))) (Finset.mem_of_mem_erase hmem)))))))) p0177
  have p0179 :=
    @g_finds (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))) (syn_wral n (syn_cnnc) (syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c)))) (syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))) (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))) (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n)))) p m M (by exact (show p ∉ (M).fv from (by exact fresh_p_not_M))) (by exact (show p ∉ ((syn_wral q (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show p ∉ ((((syn_cnnc)).fv).erase q) ∪ ((((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (((syn_cnnc)).fv).erase q from (fun hmem => (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show p ∉ (((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv).erase q from (fun hmem => (show p ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show p ∉ (((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv) ∪ (((Wff.objEq m q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show p ∉ (((syn_cin (.cv m) (.cv q))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cin (.cv m) (.cv q))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show p ∉ (((Class.cv m)).fv) ∪ (((Class.cv q)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ m from (by exact fresh_p_ne_m)))))) (show p ∉ ((Class.cv q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({q} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ q from (by exact fresh_p_ne_q)))))))))) (show p ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show p ∉ ((Wff.objEq m q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show p ∉ ({m, q} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show p ≠ m from (by exact fresh_p_ne_m)), (show p ≠ q from (by exact fresh_p_ne_q))⟩)))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show m ∉ ((syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show m ∉ ((((syn_cnnc)).fv).erase n) ∪ ((((syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))).fv).erase n) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ (((syn_cnnc)).fv).erase n from (fun hmem => (show m ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show m ∉ (((syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))).fv).erase n from (fun hmem => (show m ∉ ((syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show m ∉ (((Wff.classEq (syn_cin (.cv p) (.cv n)) (syn_c0))).fv) ∪ (((Wff.objEq p n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.classEq (syn_cin (.cv p) (.cv n)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ (((syn_cin (.cv p) (.cv n))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cin (.cv p) (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show m ∉ (((Class.cv p)).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ p from (by exact fresh_m_ne_p)))))) (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact fresh_m_ne_n)))))))))) (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((Wff.objEq p n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show m ∉ ({p, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show m ≠ p from (by exact fresh_m_ne_p)), (show m ≠ n from (by exact fresh_m_ne_n))⟩)))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show p ∉ ((syn_wral n (syn_cnnc) (syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show p ∉ ((((syn_cnnc)).fv).erase n) ∪ ((((syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c)))).fv).erase n) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (((syn_cnnc)).fv).erase n from (fun hmem => (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show p ∉ (((syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c)))).fv).erase n from (fun hmem => (show p ∉ ((syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show p ∉ (((Wff.neg (.classMem (syn_c0) (.cv n)))).fv) ∪ (((Wff.classEq (.cv n) (syn_c0c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.neg (.classMem (syn_c0) (.cv n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show p ∉ ((Wff.classMem (syn_c0) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ (((syn_c0)).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))))))))) (show p ∉ ((Wff.classEq (.cv n) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show p ∉ (((Class.cv n)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))) (show p ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show p ∉ ((syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show p ∉ ((((syn_cnnc)).fv).erase n) ∪ ((((syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n)))).fv).erase n) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (((syn_cnnc)).fv).erase n from (fun hmem => (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show p ∉ (((syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n)))).fv).erase n from (fun hmem => (show p ∉ ((syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show p ∉ (((Wff.classEq (syn_cin M (.cv n)) (syn_c0))).fv) ∪ (((Wff.classEq M (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.classEq (syn_cin M (.cv n)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show p ∉ (((syn_cin M (.cv n))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cin M (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show p ∉ ((M).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (M).fv from (by exact fresh_p_not_M)) (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))))))) (show p ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show p ∉ ((Wff.classEq M (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show p ∉ ((M).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (M).fv from (by exact fresh_p_not_M)) (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))))))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show p ∉ ((syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show p ∉ ((((syn_cnnc)).fv).erase n) ∪ ((((syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv).erase n) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (((syn_cnnc)).fv).erase n from (fun hmem => (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show p ∉ (((syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv).erase n from (fun hmem => (show p ∉ ((syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show p ∉ (((Wff.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0))).fv) ∪ (((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show p ∉ (((syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show p ∉ (((syn_cplc (.cv m) (syn_c1c))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show p ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ m from (by exact fresh_p_ne_m)))))) (show p ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))))))) (show p ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show p ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show p ∉ (((syn_cplc (.cv m) (syn_c1c))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show p ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ m from (by exact fresh_p_ne_m)))))) (show p ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))))))))))) (Finset.mem_of_mem_erase hmem)))))))) (show p ≠ m from (by exact fresh_p_ne_m)) p0044 p0059 p0070 p0075 p0080 p0094 p0178
  have p0180 :=
    @g_ineq2 (.cv n) N M
  have p0181 :=
    @g_eqeq1d (.classEq (.cv n) N) (syn_cin M (.cv n)) (syn_cin M N) (syn_c0) p0180
  have p0182 :=
    @g_eqeq2 (.cv n) N M
  have p0183 :=
    @g_orbi12d (.classEq (.cv n) N) (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq (syn_cin M N) (syn_c0)) (.classEq M (.cv n)) (.classEq M N) p0181 p0182
  have p0184 :=
    @g_rspccv (syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n))) (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N)) n N (syn_cnnc) (by exact (show n ∉ (N).fv from (by exact fresh_n_not_N))) (by exact (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ ((syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show n ∉ (((Wff.classEq (syn_cin M N) (syn_c0))).fv) ∪ (((Wff.classEq M N)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Wff.classEq (syn_cin M N) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ (((syn_cin M N)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cin M N)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show n ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (M).fv from (by exact fresh_n_not_M)) (show n ∉ (N).fv from (by exact fresh_n_not_N)))))) (show n ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show n ∉ ((Wff.classEq M N)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show n ∉ ((M).fv) ∪ ((N).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (M).fv from (by exact fresh_n_not_M)) (show n ∉ (N).fv from (by exact fresh_n_not_N))))))))))) p0183
  have p0185 :=
    @g_syl (.classMem M (syn_cnnc)) (syn_wral n (syn_cnnc) (syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n)))) (.imp (.classMem N (syn_cnnc)) (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N))) p0179 p0184
  have p0186 :=
    @g_imp (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N)) p0185
  exact p0186



#print axioms g_nndisjeq

end NFChoice.DirectNominalPrf.WPPReplay
